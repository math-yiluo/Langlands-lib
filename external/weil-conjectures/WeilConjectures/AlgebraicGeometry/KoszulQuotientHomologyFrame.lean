/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Data.Set.PowersetCard
import WeilConjectures.AlgebraicGeometry.AffineQuotientRestrictedIso
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The quotient-valued dual Koszul homology frame

Source: Stacks Project, Tag 0BQY, Lemma 48.15.4, quotient-valued Hom calculation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace ExteriorAlgebra

private theorem koszulBoundary_wedge
    (R : Type u) [CommRing R] (r n : ℕ) (f : Fin r → R)
    (v : Fin (n + 1) → (Fin r →₀ R)) :
    koszulBoundary R r f n (exteriorPower.ιMulti R (n + 1) v) =
      Finset.univ.sum (fun i : Fin (n + 1) ↦ (((-1 : R) ^ (i.val + 2)) *
        Finsupp.linearCombination R f (v i)) •
        exteriorPower.ιMulti R n (v ∘ i.succAbove)) := by
  obtain ⟨D, h1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hderivuniq⟩ :=
    koszul_differential R (Fin r →₀ R) (Finsupp.linearCombination R f)
  have hD : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm R (Fin r →₀ R)))
      (Finsupp.linearCombination R f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro z y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R (Fin r →₀ R)))
          (Finsupp.linearCombination R f) z y
  apply Subtype.ext
  simpa only [koszulBoundary, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum,
    Submodule.coe_smul, Algebra.smul_def, hD] using hform n v

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_differential_zero
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (p q : ℕ) :
    (koszulQuotientDualComplex A I r f).d p q = 0 := by
  classical
  by_cases hpq : p + 1 = q
  · subst q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext v
    have hxb : x.hom (koszulBoundary A r f p
        (exteriorPower.ιMulti A (p + 1) v)) = 0 := by
      rw [koszulBoundary_wedge, map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [map_smul]
      have hm : Finsupp.linearCombination A f (v j) ∈ I := by
        rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
        exact LinearMap.mem_range_self _ _
      change Ideal.Quotient.mk I
        (((-1 : A) ^ (j.val + 2)) * Finsupp.linearCombination A f (v j)) * _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left _ hm), zero_mul]
    simpa [koszulQuotientDualComplex, koszulQuotientDualBoundary, Linear.leftComp,
      koszulComplex, CochainComplex.of_d, ChainComplex.of_d, hxb] using
      congrArg (fun y : A ⧸ I ↦ ((-1 : A) ^ (p + 1)) • y) hxb
  · apply HomologicalComplex.shape
    simpa using hpq

end ExteriorAlgebra

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_presentation {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.affineOpens) :
    ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)),
    i ∣_ U.1 ≫ U.1.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (i.ker.ideal U))) := by
  let g := i ∣_ U.1 ≫ U.2.isoSpec.hom
  let φ := (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ g.appTop
  have hφ : φ = i.app U.1 ≫ (i ⁻¹ᵁ U.1).topIso.inv := by
    change (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (i ∣_ U.1 ≫ U.2.isoSpec.hom).appTop = _
    rw [Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Scheme.Hom.appLE_eq_app]
  have hker : RingHom.ker φ.hom = i.ker.ideal U := by
    rw [hφ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).1,
      Scheme.Hom.ker_apply]
  have hsurj : Function.Surjective φ := by
    rw [hφ]
    exact (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).2.comp
      (i.app_surjective U.1 U.2)
  have : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  let er := RingEquiv.ofBijective φ.hom.kerLift
    ⟨φ.hom.kerLift_injective, Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj⟩
  let e := Scheme.isoSpec (i ⁻¹ᵁ U.1).toScheme ≪≫ Scheme.Spec.mapIso
    er.toCommRingCatIso.op
  have he : g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (RingHom.ker φ.hom))) := by
    dsimp [e, er]
    simp only [Iso.op_hom,
      Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
    change g = (i ⁻¹ᵁ U.1).toScheme.isoSpec.hom ≫ Spec.map φ
    simp only [Scheme.isoSpec, asIso_hom, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, φ]
    simp
  have hex : ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ RingHom.ker φ.hom)),
      g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) :=
    ⟨e, he⟩
  rw [hker] at hex
  exact hex

/-- The associated sheaf of quotient-valued dual Koszul homology has its wedge frame.
Source: Stacks Project, Tag 0BQY, Lemma 48.15.4, zero-differential Hom calculation.
(blueprint: lem-y3-koszul-quotient-homology-frame).

Proof: Every generator lies in I, so multiplication by it on A/I is zero.
The Koszul boundary is an alternating sum with these coefficients; hence
precomposition into A/I is zero, including the dual-complex sign. Consequently
homology is the degree-n Hom module. Evaluation on the increasing wedge basis
identifies that module with functions from n-element subsets to A/I. The index
is finite, so this is the coproduct of copies of A/I as an A-module. Tilde and
restriction along the affine spectrum isomorphism preserve coproducts. The
quotient affine chart identifies tilde(A/I) with the restricted pushforward
of O_Z. Restriction to U also preserves coproducts, giving the claimed frame.
This needs no regularity: only that f generates I. For n>m the basis is empty,
for n=0 it is the empty wedge; m=0 and the zero quotient ring are allowed. -/
theorem koszul_quotient_homology_frame
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (n m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex
      (Γ(Y, U.1) : Type u) (i.ker.ideal U) m f).homology n
    Nonempty (T.obj Q ≅ (Scheme.Modules.restrictFunctor U.1.ι).obj
      (∐ fun _ : ULift.{u} (Set.powersetCard (Fin m) n) ↦ B)) := by
  classical
  let A := (Γ(Y, U.1) : Type u)
  let I := i.ker.ideal U
  let K := ExteriorAlgebra.koszulQuotientDualComplex A I m f
  let J := ULift.{u} (Set.powersetCard (Fin m) n)
  let b := ((Finsupp.basisSingleOne : Module.Basis (Fin m) A
    (Fin m →₀ A)).exteriorPower n).reindex Equiv.ulift.symm
  let eX : K.X n ≅ ModuleCat.of A (J →₀ (A ⧸ I)) :=
    ((ModuleCat.homLinearEquiv.trans (b.constr A).symm).trans
      (Finsupp.linearEquivFunOnFinite A (A ⧸ I) J).symm).toModuleIso
  let eH : K.homology n ≅ K.X n :=
    (ShortComplex.HomologyData.ofZeros (K.sc n)
      (ExteriorAlgebra.quotient_differential_zero A I m f hf _ _)
      (ExteriorAlgebra.quotient_differential_zero A I m f hf _ _)).left.homologyIso
  let eSum : ModuleCat.of A (J →₀ (A ⧸ I)) ≅ ∐ fun _ : J ↦ ModuleCat.of A (A ⧸ I) :=
    (ModuleCat.finsuppCoconeIsColimit A (A ⧸ I) J).coconePointUniqueUpToIso
      (coproductIsCoproduct _)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let R := Scheme.Modules.restrictFunctor U.1.ι
  obtain ⟨e, he⟩ := quotient_presentation i U
  obtain ⟨eB⟩ := affine_quotient_restricted_iso i U.1 U.2 I e he
  exact ⟨T.mapIso (eH ≪≫ eX ≪≫ eSum) ≪≫ PreservesCoproduct.iso T _ ≪≫
    Sigma.mapIso (fun _ ↦ eB) ≪≫ (PreservesCoproduct.iso R _).symm⟩

end AlgebraicGeometry
