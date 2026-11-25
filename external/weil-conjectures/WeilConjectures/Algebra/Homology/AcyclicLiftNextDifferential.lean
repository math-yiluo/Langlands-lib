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
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.AcyclicLiftSplitCycles

/-! # Lifting the next differential into the cycles of a finite tail

Source: Stacks Project, Tag 0BC9, proof, first two paragraphs.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem quotient_unit_surjective
    {R : Type u} [CommRing R] (I : Ideal R) (Z : ModuleCat.{max u v} R) :
    Function.Surjective
      ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app Z) := by
  let : Algebra R (R ⧸ I) := (Ideal.Quotient.mk I).toAlgebra
  change Function.Surjective (TensorProduct.mk R (R ⧸ I) Z 1)
  exact TensorProduct.mk_surjective R Z (R ⧸ I) (Ideal.Quotient.mk_surjective)

/-- Lift a prescribed next term's incoming differential into an exact finite projective tail.

Source: Stacks Project, Tag 0BC9, proof, first two paragraphs
(blueprint: lem-sc-acyclic-lift-next-differential).

Proof. Descend from the upper bound, splitting each epimorphism onto the next cycle
module by projectivity. The summand condition first supplies zero and invariance under
isomorphism, then puts every cycle module in P. These split exact sequences remain split
under extension of scalars. Thus the comparison identifies the reduction of the degree-n
cycle module with the cycles of E in degree n. Acyclicity of E makes its incoming
map onto these cycles surjective. Compose the prescribed term isomorphism with this map.
Under the extension/restriction adjunction it is an R-linear map from M into the reduction
of the cycle module. The quotient map to that reduction is surjective, so projectivity of
M lifts it. Its scalar extension is the prescribed surjection onto reduced cycles.
The surjectivity hypothesis makes the lifted map onto the cycle module surjective.
Compose with the cycle inclusion to obtain d. Its composite with the outgoing
old differential is zero, its image is precisely the kernel of that differential,
and its reduction obeys the required comparison equation. This argument also covers
n = b+1: the old degree-n term and its cycle module are zero. -/
theorem exists_acyclicLift_nextDifferential
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (hprojective : ∀ M, P M → Projective M)
    (hsummand : ∀ M₁ M₂ M₁₂ : ModuleCat.{max u v} R,
      P M₁ → P M₁₂ → Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂)) → P M₂)
    (hsurjective : ∀ (M₁ M₂ : ModuleCat.{max u v} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (q : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ⟶ E)
    (b n : ℤ) (hupper : C.IsStrictlyLE b)
    (hP : ∀ i, P (C.X i)) (hexact : ∀ i, n < i → C.ExactAt i)
    (hq : ∀ i, n ≤ i → IsIso (q.f i)) (hE : E.Acyclic)
    (M : ModuleCat.{max u v} R) (hM : P M)
    (e : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅ E.X (n - 1)) :
    ∃ d : M ⟶ C.X n, ∃ hd : d ≫ C.d n (n + 1) = 0,
      (ShortComplex.mk d (C.d n (n + 1)) hd).Exact ∧
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map d ≫ q.f n =
        e.hom ≫ E.d (n - 1) n  := by
  classical
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let adj := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)
  have : F.Additive := adj.left_adjoint_additive
  obtain ⟨Z, hZ, ι, hz, hzF, hmono, hS, hmonoF, hSF⟩ :=
    exists_acyclicLift_splitCycles R I P hprojective hsummand C b n hupper hP hexact
  have : Mono ι := hmono
  have : Mono (F.map ι) := hmonoF
  have : IsIso (q.f n) := hq n le_rfl
  have : IsIso (q.f (n + 1)) := hq (n + 1) (by omega)
  have hqc : q.f n ≫ E.d n (n + 1) = F.map (C.d n (n + 1)) ≫ q.f (n + 1) :=
    q.comm n (n + 1)
  let a : F.obj M ⟶ F.obj (C.X n) := e.hom ≫ E.d (n - 1) n ≫ inv (q.f n)
  have hqd : inv (q.f n) ≫ F.map (C.d n (n + 1)) =
      E.d n (n + 1) ≫ inv (q.f (n + 1)) := by
    rw [← cancel_epi (q.f n)]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [hqc]
    simp [Category.assoc]
  have ha : a ≫ F.map (C.d n (n + 1)) = 0 := by
    simp only [a, Category.assoc]
    rw [hqd]
    simp [← Category.assoc]
  let g : F.obj M ⟶ F.obj Z := (Limits.KernelFork.IsLimit.lift' hSF.fIsKernel a ha).1
  have hg : g ≫ F.map ι = a := (Limits.KernelFork.IsLimit.lift' hSF.fIsKernel a ha).2
  have hgq : g ≫ F.map ι ≫ q.f n = e.hom ≫ E.d (n - 1) n := by
    rw [← Category.assoc, hg]
    simp [a, Category.assoc]
  have hgsurj : Function.Surjective g := by
    intro z
    have hcycle : E.d n (n + 1) (q.f n ((F.map ι) z)) = 0 := by
      have hcz : F.map ι ≫ q.f n ≫ E.d n (n + 1) = 0 := by
        rw [hqc, ← Category.assoc, hzF]
        simp
      have h := congrArg (fun t ↦ t.hom z) hcz
      change (E.d n (n + 1)).hom ((q.f n).hom ((F.map ι).hom z)) =
        (0 : F.obj Z ⟶ E.X (n + 1)).hom z at h
      rw [ModuleCat.hom_zero, LinearMap.zero_apply] at h
      exact h
    have hEn := (E.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).mp (hE n)
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hEn _ hcycle
    refine ⟨e.inv x, ?_⟩
    apply (ModuleCat.mono_iff_injective (F.map ι)).mp inferInstance
    apply (ModuleCat.mono_iff_injective (q.f n)).mp inferInstance
    have h := congrArg (fun t ↦ t (e.inv x)) hgq
    change E.d (n - 1) n x = q.f n ((F.map ι) z) at hx
    change q.f n ((F.map ι) (g (e.inv x))) = E.d (n - 1) n (e.hom (e.inv x)) at h
    rw [ModuleCat.hom_inv_apply, hx] at h
    exact h
  have : Projective M := hprojective M hM
  have : Epi (adj.unit.app Z) :=
    (ModuleCat.epi_iff_surjective _).mpr (quotient_unit_surjective I Z)
  let t : M ⟶ Z := Projective.factorThru (adj.homEquiv M (F.obj Z) g) (adj.unit.app Z)
  have ht : t ≫ adj.unit.app Z = adj.homEquiv M (F.obj Z) g :=
    Projective.factorThru_comp _ _
  have hFt : F.map t = g := by
    have htrans : adj.homEquiv M (F.obj Z) (F.map t) = t ≫ adj.unit.app Z := by
      have h := adj.homEquiv_naturality_left t (𝟙 (F.obj Z))
      change adj.homEquiv M (F.obj Z) (F.map t ≫ 𝟙 _) =
        t ≫ adj.homEquiv Z (F.obj Z) (𝟙 _) at h
      rw [Category.comp_id, adj.homEquiv_id] at h
      exact h
    exact (adj.homEquiv M (F.obj Z)).injective (htrans.trans ht)
  have htsurj : Function.Surjective t :=
    hsurjective M Z t hM hZ (by
      change Function.Surjective (F.map t)
      rw [hFt]
      exact hgsurj)
  refine ⟨t ≫ ι, ?_, ?_, ?_⟩
  · simp [Category.assoc, hz]
  · rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
    intro x hx
    obtain ⟨z, hz'⟩ := hS x hx
    obtain ⟨m, rfl⟩ := htsurj z
    exact ⟨m, hz'⟩
  · change F.map (t ≫ ι) ≫ q.f n = _
    rw [F.map_comp, Category.assoc, hFt]
    exact hgq

end CochainComplex
