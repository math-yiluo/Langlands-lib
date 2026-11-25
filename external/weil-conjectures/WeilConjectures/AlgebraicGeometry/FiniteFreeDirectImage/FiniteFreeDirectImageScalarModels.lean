/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Existence of normalized scalar models

Source: Stacks Project, Tags 03EK, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
variable {X : Scheme.{u}}
  {p : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
    (a : R ⟶ S) → Presentation X a}
  (n : SheafOfModules.SuccessiveDerivedQuotient.Normalization.{u + 1, u, u + 1, u + 2}
    (C := X.ProEt) (J := ProEt.topology X)
    (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) p)

private def restrictionIso {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) : n.right a ≅ (proEtaleRingRestrictScalars a).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (proEtaleRingModules X S) (.up ℤ))
    (DerivedCategory.Qh ⋙ n.right a)
    (DerivedCategory.Qh ⋙ (proEtaleRingRestrictScalars a).mapDerivedCategory)
    (n.right a) (proEtaleRingRestrictScalars a).mapDerivedCategory
    (n.right_factors a ≪≫ (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.symm)

private theorem restrictionIso_fac
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (H : HomotopyCategory (proEtaleRingModules X S) (.up ℤ)) :
    (restrictionIso n a).hom.app (DerivedCategory.Qh.obj H) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app H =
    (n.right_factors a).hom.app H := by
  simp [restrictionIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]

private def adj {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (p a).derived ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory :=
  (n.adjunction a).ofNatIsoRight (restrictionIso n a)

private theorem adj_unit
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (proEtaleRingModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := R) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := R) (P.X i)) :
    (adj n a).unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategory.map
        ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
        (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((n.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P)) := by
  simp only [adj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← (restrictionIso n a).hom.naturality_assoc]
  simp only [Functor.comp_obj]
  rw [restrictionIso_fac]
  exact n.adjunction_normalization a P hP hf

private def ordinaryUnit (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (p (𝟙 R)).ordinary ≅ 𝟭 (proEtaleRingModules X R) :=
  (n.ordinaryAdjunction (𝟙 R)).leftAdjointIdIso (Iso.refl _)

private theorem ordinaryUnit_pure
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U) :
    ((ordinaryUnit n R).hom.app M).val.app U
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U r x) = r • x := by
  have hp : SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U r x =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (p (𝟙 R)) M U 1 (r • x) := by
    unfold SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
      SheafOfModules.SuccessiveDerivedQuotient.pure
    let : Module (R.obj.obj U) (R.obj.obj U) :=
      Module.compHom _ ((𝟙 R : R ⟶ R).hom.app U).hom
    congr 2
    have ht := (TensorProduct.tmul_smul (R := R.obj.obj U) r (1 : R.obj.obj U) x).symm
    change (r * 1) ⊗ₜ[R.obj.obj U] x = (1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] (r • x) at ht
    simpa only [mul_one] using ht
  have hm : (ordinaryUnit n R).hom.app M =
      (n.ordinaryAdjunction (𝟙 R)).counit.app M := by
    rw [ordinaryUnit, Adjunction.leftAdjointIdIso_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hm, hp, ← n.ordinary_unit]
  have ht := congrArg (fun f ↦ f.val.app U (r • x))
    ((n.ordinaryAdjunction (𝟙 R)).right_triangle_components M)
  exact ht

private def ordinaryUnitHomotopy
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (proEtaleRingModules X R) (.up ℤ)) :=
  let e : (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      (𝟭 (proEtaleRingModules X R)).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory (ordinaryUnit n R).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory (ordinaryUnit n R).inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  e ≪≫ Functor.mapHomotopyCategoryIdIso (proEtaleRingModules X R) (.up ℤ)

include n in
private theorem unitCounitIsIso
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    IsIso (p (𝟙 R)).counit := by
  let e : (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh :=
    isoWhiskerRight (ordinaryUnitHomotopy n R) DerivedCategory.Qh ≪≫
      DerivedCategory.Qh.leftUnitor
  let := (p (𝟙 R)).universal
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ)) _ _
    ((MorphismProperty.IsInvertedBy.iff_of_iso
      (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ)) e).mpr
      (Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ))))

private def derivedUnit
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (p (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (proEtaleRingModules X R)) := by
  letI := unitCounitIsIso n R
  exact Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ))
    (DerivedCategory.Qh ⋙ (p (𝟙 R)).derived)
    (DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (proEtaleRingModules X R)))
    (p (𝟙 R)).derived (𝟭 _)
    (asIso (p (𝟙 R)).counit ≪≫
      isoWhiskerRight (ordinaryUnitHomotopy n R) DerivedCategory.Qh ≪≫
      DerivedCategory.Qh.leftUnitor ≪≫ DerivedCategory.Qh.rightUnitor.symm)

private theorem derivedUnit_normalization
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ)) :
    (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (ordinaryUnit n R).hom (.up ℤ)).app H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso (proEtaleRingModules X R) (.up ℤ)).hom.app H) := by
  simp [derivedUnit, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    ordinaryUnitHomotopy]

/-- Normalized scalar models exist on the actual pro-etale module categories.
Source: Stacks Project, Tags 03EK, 06YY and 07A6.
(blueprint: lem-sp-finite-free-scalar-models).

Proof: take the universal presentations and their coherent normalization from
successive_derived_quotient_normalization. The two localization factorizations
identify its right adjoints with the actual exact scalar restrictions. Transport
the adjunctions along these identifications; naturality gives the required unit
normalization. For the identity ring map, restriction is the identity. The ordinary
adjunction therefore gives multiplication as an isomorphism. Its triangle identity
and tensor balancing show that r tensor x maps to r x. The induced homotopy
isomorphism shows that the identity scalar functor inverts quasi-isomorphisms.
Its universal derived counit is consequently invertible. Localize this counit
followed by ordinary multiplication to obtain the derived multiplication; the
localization factorization gives exactly the required formula. -/
theorem finiteFreeDirectImageScalarModels (X : Scheme.{u}) : Nonempty (ScalarModel X) := by
  obtain ⟨p, ⟨n⟩⟩ :=
    SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization
      (C := X.ProEt) (J := ProEt.topology X)
      (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T)
  exact ⟨{
    presentation := p
    normalization := n
    adjunction := adj n
    adjunction_unit := adj_unit n
    ordinaryUnit := ordinaryUnit n
    ordinaryUnit_pure := ordinaryUnit_pure n
    unit := derivedUnit n
    unit_normalization := derivedUnit_normalization n }⟩

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
