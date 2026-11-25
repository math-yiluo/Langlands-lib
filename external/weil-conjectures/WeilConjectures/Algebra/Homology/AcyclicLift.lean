/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import WeilConjectures.Algebra.Homology.AcyclicLiftTailExtension
import Mathlib.LinearAlgebra.Prod
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Tactic.Choose

/-!
# Lifting bounded-above acyclic complexes modulo an ideal

Source: Stacks Project, More on Algebra, Tag 0BC9, lemma-lift-acyclic-complex
(blueprint: lem-sc-complex-lift-acyclic-projective).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

/-- Stacks Project, Tag 0BC9 (blueprint: lem-sc-complex-lift-acyclic-projective).
Reduction modulo `I` is extension of scalars to `R ⧸ I`, canonically `P / IP`.
The direct-sum condition is stated for any module isomorphic to the binary direct sum,
as membership in a class of modules is understood up to isomorphism.

Proof: The summand condition gives zero membership and closure under isomorphism.
Start with the zero tail above an upper bound b. Repeatedly apply the one-degree
extension theorem to obtain a sequence of finite lift tails and compatible comparison
maps. In each fixed degree the transition maps eventually become isomorphisms.
Take the degreewise colimit. Eventual constancy identifies its terms with the terms
of finite tails, proving class membership and vanishing above b. Choose a stage
containing a degree and both its neighbors: its short complex is isomorphic to the
colimit's short complex, which transfers exactness. Extension of scalars preserves
the colimit, so the compatible reduction comparisons descend to a comparison with E.
Every component of that comparison is an isomorphism, giving the required complex
isomorphism. The finite extension is the only remaining proof dependency. -/
theorem exists_acyclic_lift_mod_ideal
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (hprojective : ∀ M, P M → Projective M)
    (hsummand : ∀ M₁ M₂ M₁₂ : ModuleCat.{max u v} R,
      P M₁ → P M₁₂ → Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂)) → P M₂)
    (hsurjective : ∀ (M₁ M₂ : ModuleCat.{max u v} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hbounded : ∃ b : ℤ, E.IsStrictlyLE b)
    (hacyclic : E.Acyclic)
    (hterms : ∀ i : ℤ, ∃ M : ModuleCat.{max u v} R, P M ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅ E.X i)) :
    ∃ A : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, A.IsStrictlyLE b) ∧ A.Acyclic ∧ (∀ i : ℤ, P (A.X i)) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A ≅ E) := by
  classical
  obtain ⟨b, hb⟩ := hbounded
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Z : ModuleCat.{max u v} R := ModuleCat.of R PUnit
  have hZ : Limits.IsZero Z := ModuleCat.isZero_of_subsingleton Z
  obtain ⟨M, hM, _⟩ := hterms b
  have hPZ : P Z := hsummand M Z M hM hM
    ⟨(LinearEquiv.prodUnique (R := R) (M := M) (M₂ := Z)).symm.toModuleIso⟩
  have hPiso : ∀ (M N : ModuleCat.{max u v} R), P M → (M ≅ N) → P N := by
    intro M N hM e
    exact hsummand Z N M hPZ hM
      ⟨e ≪≫ (LinearEquiv.uniqueProd (R := R) (M := N) (M₂ := Z)).symm.toModuleIso⟩
  let K : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    { X := fun _ => Z, d := fun _ _ => 0 }
  let seed : AcyclicLiftTail R I P E b (b + 1) :=
    { complex := K
      comparison := 0
      lower := (K.isStrictlyGE_iff _).2 (fun _ _ => hZ)
      upper := (K.isStrictlyLE_iff _).2 (fun _ _ => hZ)
      terms := fun _ => hPZ
      exact := fun i _ => HomologicalComplex.ExactAt.of_isZero hZ
      iso := fun i hi => by
        have : E.IsStrictlyLE b := hb
        exact (Functor.map_isZero F hZ).isIso
          (E.isZero_of_isStrictlyLE b i (by omega)) _ }
  let State := fun n : ℕ => AcyclicLiftTail R I P E b (b + 1 - n)
  have step : ∀ (n : ℕ) (T : State n),
      ∃ T' : State (n + 1), ∃ f : T.complex ⟶ T'.complex,
        (∀ i, b + 1 - (n : ℤ) ≤ i → IsIso (f.f i)) ∧
        G.map f ≫ T'.comparison = T.comparison := by
    intro n T
    have hn : b + 1 - ((n + 1 : ℕ) : ℤ) = (b + 1 - n) - 1 := by omega
    obtain ⟨T', f, hf, hc⟩ := exists_extend_acyclicLiftTail R I P hprojective hsummand
      hsurjective E hacyclic hterms b (b + 1 - n) (by omega) T
    let T'' : State (n + 1) :=
      { complex := T'.complex
        comparison := T'.comparison
        lower := by simpa only [hn] using T'.lower
        upper := T'.upper
        terms := T'.terms
        exact := by simpa only [hn] using T'.exact
        iso := by simpa only [hn] using T'.iso }
    exact ⟨T'', f, hf, hc⟩
  choose next arrow arrow_iso arrow_comm using step
  let T : ∀ n, State n := fun n => Nat.rec (by simpa [State] using seed) next n
  let f : ∀ n, (T n).complex ⟶ (T (n + 1)).complex := fun n => arrow n (T n)
  have hf : ∀ (n : ℕ) (i : ℤ), b + 1 - (n : ℤ) ≤ i → IsIso ((f n).f i) :=
    fun n => arrow_iso n (T n)
  have hc : ∀ n, G.map (f n) ≫ (T (n + 1)).comparison = (T n).comparison :=
    fun n => arrow_comm n (T n)
  let D := Functor.ofSequence f
  let A := Limits.colimit D
  have stable : ∀ (i : ℤ) (n : ℕ), b + 1 - (n : ℤ) ≤ i →
      Functor.IsEventuallyConstantFrom
        (D ⋙ HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i) n := by
    intro i n hi m φ
    change IsIso ((D.map φ).f i)
    have hnm := leOfHom φ
    induction m, hnm using Nat.le_induction with
    | base =>
        have he : φ = 𝟙 n := Subsingleton.elim _ _
        simp only [he]
        change IsIso ((D.map (𝟙 n)).f i)
        rw [D.map_id]
        change IsIso (𝟙 ((T n).complex.X i))
        infer_instance
    | succ m hnm ih =>
        have hp : IsIso ((D.map (homOfLE hnm)).f i) := ih (homOfLE hnm)
        have hs : IsIso ((f m).f i) := hf m i (by omega)
        have he : φ = homOfLE hnm ≫ homOfLE (Nat.le_add_right m 1) :=
          Subsingleton.elim _ _
        rw [he, Functor.map_comp, HomologicalComplex.comp_f]
        rw [show D.map (homOfLE (Nat.le_add_right m 1)) = f m from
          Functor.ofSequence_map_homOfLE_succ f m]
        infer_instance
  have hiota : ∀ (i : ℤ) (n : ℕ), b + 1 - (n : ℤ) ≤ i →
      IsIso ((Limits.colimit.ι D n).f i) := by
    intro i n hi
    exact (stable i n hi).isIso_ι_of_isColimit
      (Limits.isColimitOfPreserves
        (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i)
        (Limits.colimit.isColimit D))
  have below : ∀ i : ℤ, ∃ n : ℕ, b + 1 - (n : ℤ) < i := by
    intro i
    refine ⟨(b + 2 - i).toNat, ?_⟩
    omega
  have hAterms : ∀ i, P (A.X i) := by
    intro i
    obtain ⟨n, hn⟩ := below i
    have := hiota i n (by omega)
    exact hPiso _ _ ((T n).terms i) (asIso ((Limits.colimit.ι D n).f i))
  have hAbounded : A.IsStrictlyLE b := by
    apply (A.isStrictlyLE_iff b).2
    intro i hi
    obtain ⟨n, hn⟩ := below i
    have := hiota i n (by omega)
    have : (T n).complex.IsStrictlyLE b := (T n).upper
    exact ((T n).complex.isZero_of_isStrictlyLE b i hi).of_iso
      (asIso ((Limits.colimit.ι D n).f i)).symm
  have hAexact : A.Acyclic := by
    intro i
    obtain ⟨n, hn⟩ := below (i - 1)
    let q := (HomologicalComplex.shortComplexFunctor
      (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i).map (Limits.colimit.ι D n)
    have h₁ : IsIso q.τ₁ := by
      have hp : (ComplexShape.up ℤ).prev i = i - 1 :=
        ComplexShape.prev_eq' _ (by change i - 1 + 1 = i; omega)
      change IsIso ((Limits.colimit.ι D n).f ((ComplexShape.up ℤ).prev i))
      rw [hp]
      exact hiota (i - 1) n (by omega)
    have h₂ : IsIso q.τ₂ := hiota i n (by omega)
    have h₃ : IsIso q.τ₃ := by
      have hp : (ComplexShape.up ℤ).next i = i + 1 := ComplexShape.next_eq' _ rfl
      change IsIso ((Limits.colimit.ι D n).f ((ComplexShape.up ℤ).next i))
      rw [hp]
      exact hiota (i + 1) n (by omega)
    have : IsIso q := ShortComplex.isIso_of_isIso q
    exact ShortComplex.exact_of_iso (asIso q) ((T n).exact i (by omega))
  let s : Limits.Cocone (D ⋙ G) :=
    { pt := E
      ι := NatTrans.ofSequence (fun n => (T n).comparison) (by
        intro n
        simpa [D] using hc n) }
  let hcol := Limits.isColimitOfPreserves G (Limits.colimit.isColimit D)
  let e : G.obj A ⟶ E := hcol.desc s
  have he : ∀ n, G.map (Limits.colimit.ι D n) ≫ e = (T n).comparison :=
    fun n => hcol.fac s n
  have heiso : ∀ i, IsIso (e.f i) := by
    intro i
    obtain ⟨n, hn⟩ := below i
    have := hiota i n (by omega)
    have : IsIso ((G.map (Limits.colimit.ι D n)).f i) := by
      change IsIso (F.map ((Limits.colimit.ι D n).f i))
      infer_instance
    have : IsIso ((T n).comparison.f i) := (T n).iso i (by omega)
    have h := congrArg (fun q => q.f i) (he n)
    exact IsIso.of_isIso_fac_left h
  have : IsIso e := HomologicalComplex.Hom.isIso_of_components e
  exact ⟨A, ⟨b, hAbounded⟩, hAexact, hAterms, ⟨asIso e⟩⟩

end CochainComplex
