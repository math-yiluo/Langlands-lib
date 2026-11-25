/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-!
# Ordinary pro-etale operations with arbitrary constant coefficients

This supplies the arbitrary-constant-ring specialization of the ring-sheaf
operations. The intrinsic finite-coefficient interface remains available.

## References

* Stacks Project, Modules on Sites, and Tag 0H7J
* Stacks, Section 0735
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- The specified constant-section comparison is invertible for arbitrary rings. -/
theorem proEtaleConstantRingComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A) := by
  -- Compare the two left adjoints to sections at the base-changed terminal object.
  let D := CommRingCat.{u + 1}
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT : IsTerminal ((proEtaleBaseChange f).obj T) :=
    hT.isTerminalObj (proEtaleBaseChange f)
  let eR : proEtaleSheafDirectImage f D ⋙
      (sheafSections (ProEt.topology Y) D).obj (Opposite.op T) ≅
        (sheafSections (ProEt.topology X) D).obj (Opposite.op ((proEtaleBaseChange f).obj T)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let adj₁ := ((constantSheafAdj (ProEt.topology Y) D hT).comp
    (proEtaleSheafAdjunction f D)).ofNatIsoRight eR
  let adj₂ := constantSheafAdj (ProEt.topology X) D hGT
  let e := adj₁.leftAdjointUniq adj₂
  -- Identify the specified map by its transpose, including its constant-section normalization.
  have he : proEtaleCoefficientInverseImageMap f A =
      e.hom.app (CommRingCat.of (ULift.{u + 1, u} A)) := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj₁, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    unfold proEtaleCoefficientInverseImageMap proEtaleConstantInverseImageMap
    rw [← Adjunction.homEquiv_symm_apply]
    dsimp only [D, proEtaleSheafDirectImage, ProEtale.lowerStar,
      proEtaleConstantRing, Functor.comp_obj] at *
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    change (constantSheafAdj (ProEt.topology Y) D hT).homEquiv _ _
      (proEtaleConstantDirectImageMap f D (CommRingCat.of (ULift.{u + 1, u} A))) =
        adj₂.unit.app _
    unfold proEtaleConstantDirectImageMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj D hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [adj₂, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rfl
  rw [he]
  infer_instance

attribute [instance] proEtaleConstantRingComparison_isIso

/-- The coefficient identification fixed by the constant-section map, with no finiteness. -/
noncomputable def proEtaleConstantRingComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A) ≅
      proEtaleConstantRing X A :=
  asIso (proEtaleCoefficientInverseImageMap f A)

/-- Ordinary module inverse image in the intrinsic constant-ring presentation. -/
noncomputable abbrev proEtaleConstantRingPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- Ordinary module direct image with the adjoint constant-section scalar action. -/
noncomputable abbrev proEtaleConstantRingPushforward (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The tensor-unit-normalized adjunction of the arbitrary constant-ring operations. -/
noncomputable abbrev proEtaleConstantRingAdjunction (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- Exact termwise descent to the same ordinary unbounded intrinsic derived category. -/
noncomputable abbrev proEtaleConstantRingDerivedPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  (proEtaleConstantRingPullback A f).mapDerivedCategory

end AlgebraicGeometry.Scheme
