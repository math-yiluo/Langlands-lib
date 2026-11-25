/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Splicing a prescribed incoming differential into a cochain complex

Source: Stacks Project, Tag 0BC9, proof, extension of the diagram to the left.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory

namespace CochainComplex

/-- Splice an already constructed differential and compatible term comparison into a tail.

Source: Stacks Project, Tag 0BC9, proof, final sentence of the second paragraph
(blueprint: lem-sc-splice-incoming-differential).

Proof. Replace the term in degree n-1 by M, keeping every other term of C.
The new outgoing differential is d, transported along the equality (n-1)+1=n.
All other differentials are the old ones, except the incoming map to M, which is
zero. The old degree n-2 term is zero by the lower support bound. Composites of
successive differentials therefore vanish: the only nontrivial new check is hd.
The identity maps away from n-1 and the zero map in degree n-1 define f, since
C was zero below n. Define q' by the old comparison away from n-1 and e.hom
in that degree. The supplied compatibility proves its outgoing square, and its
incoming square has zero source. The composite comparison equals q degreewise,
including degree n-1 where the old source is zero. In every unchanged degree
q' and f have the stated components and are isomorphisms when q is.
Exactness at n is the assumed exactness of M -> C^n -> C^(n+1), transported
by the term equalities. For i>n, all three terms and both differentials of the
short complex computing exactness are unchanged, so exactness transfers. No
projectivity, quotient-surjectivity, term class, or upper support bound is used. -/
theorem exists_spliceIncomingDifferential
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (C : CochainComplex A ℤ) (E : CochainComplex B ℤ)
    (q : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶ E)
    (n : ℤ) (hlower : C.IsStrictlyGE n)
    (M : A) (d : M ⟶ C.X n) (hd : d ≫ C.d n (n + 1) = 0)
    (hexact : (ShortComplex.mk d (C.d n (n + 1)) hd).Exact)
    (e : F.obj M ≅ E.X (n - 1))
    (hcomm : F.map d ≫ q.f n = e.hom ≫ E.d (n - 1) n) :
    ∃ D : CochainComplex A ℤ,
      ∃ f : C ⟶ D,
        ∃ q' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj D ⟶ E,
          (∀ i, D.X i = if i = n - 1 then M else C.X i) ∧
          (∀ i, n ≤ i → IsIso (f.f i)) ∧
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫ q' = q ∧
          IsIso (q'.f (n - 1)) ∧
          (∀ i, n ≤ i → IsIso (q.f i) → IsIso (q'.f i)) ∧
          D.ExactAt n ∧
          (∀ i, n < i → C.ExactAt i → D.ExactAt i) := by
  generalize hk : n - 1 = k at *
  have hn : n = k + 1 := by omega
  subst n
  let X : ℤ → A := fun i ↦ if i = k then M else C.X i
  have hXold (i : ℤ) (hi : i ≠ k) : X i = C.X i := by simp [X, hi]
  let δ : ∀ i : ℤ, X i ⟶ X (i + 1) := fun i ↦
    if hi : i = k then
      eqToHom (by simp [X, hi]) ≫ d ≫
        eqToHom (by simp [X, hi, show k + 1 ≠ k by omega])
    else if hj : i + 1 = k then 0
    else eqToHom (hXold i hi) ≫ C.d i (i + 1) ≫
      eqToHom (hXold (i + 1) hj).symm
  have hδ (i : ℤ) : δ i ≫ δ (i + 1) = 0 := by
    by_cases hi : i = k
    · subst i
      have h₁ : k + 1 ≠ k := by omega
      have h₂ : k + 1 + 1 ≠ k := by omega
      simp only [h₂, h₁, ↓reduceDIte, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, Preadditive.IsIso.comp_left_eq_zero, X, δ]
      rw [← Category.assoc, hd]
      simp
    · by_cases hj : i + 1 = k
      · simp [δ, hi, hj]
      · by_cases hk : i + 1 + 1 = k
        · simp [δ, hi, hj, hk]
        · simp [δ, hi, hj, hk, Category.assoc]
  let D : CochainComplex A ℤ := CochainComplex.of X δ hδ
  let φ : ∀ i : ℤ, C.X i ⟶ X i := fun i ↦
    if hi : i = k then 0 else eqToHom (hXold i hi).symm
  have hφ (i : ℤ) : φ i ≫ D.d i (i + 1) = C.d i (i + 1) ≫ φ (i + 1) := by
    have : C.IsStrictlyGE (k + 1) := hlower
    by_cases hi : i = k
    · subst i
      rw [(C.isZero_of_isStrictlyGE (k + 1) k (by omega)).eq_of_src
        (C.d k (k + 1)) 0]
      simp [φ, D]
    · by_cases hj : i + 1 = k
      · have hz := C.isZero_of_isStrictlyGE (k + 1) i (by omega)
        exact hz.eq_of_src _ _
      · simp [φ, D, δ, hi, hj]
  let f : C ⟶ D := CochainComplex.ofHom φ hφ
  let ψ : ∀ i : ℤ, F.obj (X i) ⟶ E.X i := fun i ↦
    if hi : i = k then
      F.map (eqToHom (by simp [X, hi])) ≫ e.hom ≫ eqToHom (by rw [hi])
    else F.map (eqToHom (hXold i hi)) ≫ q.f i
  have hψ (i : ℤ) :
      ψ i ≫ E.d i (i + 1) = F.map (D.d i (i + 1)) ≫ ψ (i + 1) := by
    by_cases hi : i = k
    · subst i
      have h₁ : (k + 1) ≠ k := by omega
      simp [ψ, D, δ, X, h₁, Functor.map_comp, Category.assoc,
        ← hcomm]
    · by_cases hj : i + 1 = k
      · have : C.IsStrictlyGE (k + 1) := hlower
        have hz : CategoryTheory.Limits.IsZero (F.obj (X i)) := by
          rw [hXold i hi]
          exact F.map_isZero (C.isZero_of_isStrictlyGE (k + 1) i (by omega))
        exact hz.eq_of_src _ _
      · simp [ψ, D, δ, hi, hj, Functor.map_comp, Category.assoc]
  let q' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj D ⟶ E :=
    CochainComplex.ofHom ψ hψ
  refine ⟨D, f, q', fun i ↦ rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hik : i ≠ k := by omega
    dsimp only [f, CochainComplex.ofHom, φ]
    rw [dite_eq_right hik]
    infer_instance
  · ext i
    by_cases hi : i = k
    · subst i
      have : C.IsStrictlyGE (k + 1) := hlower
      exact (F.map_isZero (C.isZero_of_isStrictlyGE (k + 1) k (by omega))).eq_of_src _ _
    · simp [f, q', φ, ψ, hi]
  · dsimp only [q', CochainComplex.ofHom, ψ]
    simp only [dite_true]
    infer_instance
  · intro i hi hqi
    have : IsIso (q.f i) := hqi
    have hik : i ≠ k := by omega
    dsimp only [q', CochainComplex.ofHom, ψ]
    rw [dite_eq_right hik]
    infer_instance
  · have h₁ : k + 1 ≠ k := by omega
    have h₂ : k + 1 + 1 ≠ k := by omega
    let α : D.sc' k (k + 1) (k + 1 + 1) ≅
        ShortComplex.mk d (C.d (k + 1) (k + 1 + 1)) hd :=
      ShortComplex.isoMk (eqToIso (by simp [D, X]))
        (eqToIso (hXold (k + 1) h₁)) (eqToIso (hXold (k + 1 + 1) h₂))
        (by simp [D, δ, X, h₁]) (by simp [D, δ, h₁, h₂])
    apply (D.exactAt_iff' k (k + 1) (k + 1 + 1) (by simp) (by simp)).mpr
    exact (ShortComplex.exact_iff_of_iso α).mpr hexact
  · intro i hi hCi
    have h₀ : i - 1 ≠ k := by omega
    have h₁ : i ≠ k := by omega
    have h₂ : i + 1 ≠ k := by omega
    let α : D.sc' (i - 1) i (i + 1) ≅ C.sc' (i - 1) i (i + 1) :=
      ShortComplex.isoMk (eqToIso (hXold (i - 1) h₀))
        (eqToIso (hXold i h₁)) (eqToIso (hXold (i + 1) h₂))
        (by simp [D, CochainComplex.of.d, δ, h₀, h₁])
        (by simp [D, δ, h₁, h₂])
    apply (D.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mpr
    exact (ShortComplex.exact_iff_of_iso α).mpr
      ((C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp hCi)

end CochainComplex
