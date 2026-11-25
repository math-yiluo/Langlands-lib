/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange

/-!
# The product of a single Kummer boundary

The iterated cup product with supports of Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`) of a one-element tuple `(f₁)` is
`∂κ(f₁) ∪ 1`, the cup product of the Kummer boundary `∂κ(f₁)` with the unit class supported
everywhere. By the *right unit law* of the cup product with supports with Tate coefficients, it is
the Kummer boundary `∂κ(f₁)` itself, read as a class with supports in `V(f₁)` and coefficients
`Λ(1)[2]`; the same holds after any base change.

The right unit law mirrors the left one of `WeilConjectures.EtaleCohomology.Purity.Smooth.
KummerProductAppend` and `WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc`: it comes from
`HasTateTwist.twistObjectAddIso_zero_right`, the compatibility of the right unitor of the derived
tensor product with the shifts (`DerivedCategory.rightUnitor_commShift_app`), and the fact that the
diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` is also a section of the right unitor (`λ_𝟙 = ρ_𝟙`).

## Main statements

- `DerivedCategory.rightUnitor_commShift_app`
- `AlgebraicGeometry.Etale.supportedProduct_liftCounitOfRangeEqUniv_right`
- `AlgebraicGeometry.Etale.cupWithSupports_liftCounitOfRangeEqUniv_right`
- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_zero_right`
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject_kummerBoundaryProduct_zero_right`
- `AlgebraicGeometry.Etale.kummerBoundaryProduct_one`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_one`
-/

@[expose] public section

universe w v t u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

section RightUnitor

variable (C : Type t) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_rightUnitorShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

open TensorCommShift₂ in
/-- The right unitor of `D(C)` commutes with the shifts at the image of a K-flat complex. -/
lemma rightUnitor_commShift_app_kFlat (P : CochainComplex.KFlat C) (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).commShiftIso n).hom.app
        ((LKFlat C).obj P) ≫ (ρ_ ((LKFlat C).obj P)).hom⟦n⟧' =
      (ρ_ (((LKFlat C).obj P)⟦n⟧)).hom := by
  -- Fix the coproduct universe before constructing the tensor and K-flat shift instances.
  have : HasCoproducts.{0} C := inferInstance
  -- Reuse the tensor structures throughout the localization comparison.
  let : MonoidalCategoryStruct (CochainComplex C ℤ) :=
    HomologicalComplex.monoidalCategoryStruct C (.up ℤ)
  let : MonoidalCategory (CochainComplex C ℤ) := inferInstance
  let : MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  let : MonoidalCategoryStruct (HomotopyCategory C (.up ℤ)) := inferInstance
  let : MonoidalCategoryStruct (DerivedCategory C) := inferInstance
  let a := ((CochainComplex.ιKFlat C).commShiftIso n).hom.app P
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)
  have h₁ := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
    (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)) n P
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  have hr (P : CochainComplex.KFlat C) : (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
      (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
      (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app P ≫ (L C).map (ρ_ P.obj).hom =
        (ρ_ ((LKFlat C).obj P)).hom := by
    have h := DerivedMonoidal.rightUnitor_hom_app Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C _).obj P.obj)
    have h' := HomotopyCategory.MonoidalCategory.rightUnitor_hom_app P.obj
    exact (congrArg (_ ≫ Qh.map ·) h'.symm).trans h.symm
  have h₂ : (((F C).flip.obj (𝟙_ _)).commShiftIso n).hom.app P =
      (L C).map (a ▷ 𝟙_ _ ≫
        (CochainComplex.mapBifunctorShift₁Iso P.obj (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
    rfl
  have h₃ : ((LKFlat C).commShiftIso n).hom.app P =
      (L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  rw [h₂, h₃] at h₁
  simp only [Category.assoc] at h₁
  have hA : ((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj) ≫
        (ρ_ (((LKFlat C).obj P)⟦n⟧)).hom =
      (ρ_ ((LKFlat C).obj (P⟦n⟧))).hom ≫ (L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj :=
    rightUnitor_naturality _
  have hC : (ρ_ ((LKFlat C).obj P)).hom = (Functor.CommShift₂OfLocalization.liftingIsoApp
      (L C) (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
      (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app P ≫
        (L C).map (ρ_ P.obj).hom :=
    (hr P).symm
  have hE := ((L C).commShiftIso_hom_naturality (ρ_ P.obj).hom n).symm
  have hF := CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom P.obj n
  have hN := rightUnitor_naturality a
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj)), hA]
  have hB := hr (P⟦n⟧)
  rw [← hB, hC, (shiftFunctor (DerivedCategory C) n).map_comp]
  erw [reassoc_of% h₁]
  rw [Category.assoc]
  congr 1
  have hG : (L C).map (a ▷ 𝟙_ _ ≫
      (CochainComplex.mapBifunctorShift₁Iso P.obj (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ ≫ ((L C).map (ρ_ P.obj).hom)⟦n⟧' =
      (L C).map (ρ_ ((P⟦n⟧).obj)).hom ≫ (L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj := by
    erw [hE]
    rw [← Functor.map_comp_assoc, Category.assoc, hF]
    erw [hN]
    rw [Functor.map_comp_assoc]
    rfl
  exact hG

open TensorCommShift₂ in
/-- The right unitor of `D(C)` commutes with the shifts: the commutation of `- ⊗ᴸ 𝟙_` with the
shift by `n`, followed by the shifted unitor, is the unitor of the shifted object. -/
lemma rightUnitor_commShift_app (K : DerivedCategory C) (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).commShiftIso n).hom.app K ≫
      (ρ_ K).hom⟦n⟧' = (ρ_ (K⟦n⟧)).hom := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  let e := (LKFlat C).objObjPreimageIso K
  have h := rightUnitor_commShift_app_kFlat C ((LKFlat C).objPreimage K) n
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map (e.hom⟦n⟧'))]
  have h₁ := (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).commShiftIso n).hom.naturality
    e.hom
  simp only [Functor.comp_map] at h₁
  rw [reassoc_of% h₁, ← Functor.map_comp]
  erw [rightUnitor_naturality]
  rw [Functor.map_comp, reassoc_of% h]
  exact (rightUnitor_naturality _).symm

end RightUnitor

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Shift

/-- `K⟦0⟧⟦a⟧ ≅ K⟦0 + a⟧` is the identification `K⟦0⟧ ≅ K`, shifted by `a`. -/
lemma shiftFunctorAdd'_zero_add_inv_app_eq {D : Type*} [Category D] [HasShift D ℤ] (K : D)
    (a c : ℤ) (h : 0 + a = c) :
    (shiftFunctorAdd' D 0 a c h).inv.app K =
      ((shiftFunctorZero D ℤ).hom.app K)⟦a⟧' ≫ eqToHom (by rw [← h, zero_add]; rfl) := by
  obtain rfl : c = a := by omega
  simp [shiftFunctorAdd'_zero_add]

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The right unitor of the derived tensor product commutes with the shifts
(`DerivedCategory.rightUnitor_commShift_app`). -/
lemma derivedTensorRightUnitor_commShift (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (n : ℤ) :
    (((derivedTensor A X).flip.obj (𝟙_ _)).commShiftIso n).hom.app K ≫
        (derivedTensorRightUnitor A X K).hom⟦n⟧' = (derivedTensorRightUnitor A X (K⟦n⟧)).hom :=
  DerivedCategory.rightUnitor_commShift_app _ K n

/-- The tensor product of an identity with a morphism `g` is `K ⊗ᴸ g`. -/
lemma derivedTensorHom_id_left (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : M ⟶ M') :
    derivedTensorHom A (𝟙 K) g = ((derivedTensor A X).obj K).map g := by
  simp [derivedTensorHom]

/-- Naturality of the commutation of `- ⊗ᴸ N` with the shifts in the variable `N`. -/
@[reassoc]
lemma derivedTensor_obj_map_comp_flip_commShiftIso_hom_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : N ⟶ N') (a : ℤ) :
    ((derivedTensor A X).obj (K⟦a⟧)).map g ≫
        (((derivedTensor A X).flip.obj N').commShiftIso a).hom.app K =
      (((derivedTensor A X).flip.obj N).commShiftIso a).hom.app K ≫
        (((derivedTensor A X).obj K).map g)⟦a⟧' :=
  (NatTrans.shift_app_comm ((derivedTensor A X).flip.map g) a K).symm

/-- Naturality of the right unitor of the derived tensor product. -/
@[reassoc]
lemma derivedTensorHom_comp_derivedTensorRightUnitor_hom
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    derivedTensorHom A f (𝟙 (𝟙_ _)) ≫ (derivedTensorRightUnitor A X M').hom =
      (derivedTensorRightUnitor A X M).hom ≫ f := by
  rw [derivedTensorHom_eq_tensorHom, tensorHom_id]
  exact rightUnitor_naturality f

/-- The identification `K⟦a⟧ ⊗ M⟦b⟧ ≅ (K ⊗ M)⟦a + b⟧`
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`) for `b = 0` is the commutation of `- ⊗ M` with
the shift by `a`. -/
lemma derivedTensorHom_shiftFunctorZero'_inv_comp_derivedTensorShiftIso_hom_right
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a b : ℤ) (hb : b = 0) :
    derivedTensorHom A (𝟙 (K⟦a⟧)) ((shiftFunctorZero' _ b hb).inv.app M) ≫
        (derivedTensorShiftIso A K M a b).hom =
      (((derivedTensor A X).flip.obj M).commShiftIso a).hom.app K ≫
        eqToHom (by rw [hb, add_zero]; rfl) := by
  subst hb
  simp only [derivedTensorShiftIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, shiftFunctorAdd'_zero_add_inv_app_eq, derivedTensorHom_id_left]
  have inner : ((derivedTensor A X).obj K).map ((shiftFunctorZero _ ℤ).inv.app M) ≫
      ((derivedTensor A X).obj K).map ((shiftFunctorZero _ ℤ).hom.app M) ≫
        (shiftFunctorZero _ ℤ).inv.app (((derivedTensor A X).obj K).obj M) =
      (shiftFunctorZero _ ℤ).inv.app (((derivedTensor A X).obj K).obj M) := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [derivedTensor_obj_map_comp_flip_commShiftIso_hom_app_assoc, ← Functor.map_comp_assoc,
    inner, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end Shift

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Product

variable {U Z₂ Z : Scheme.{u}}

/-- **The right unit law of the product of supports.** For a surjective closed immersion `i₂`,
the product with the class `u : Λ_U ⟶ Ri₂_! Ri₂^! N` supported everywhere lifting
`φ : Λ_U ⟶ N` is `Ri_! Ri^! M ⊗ Λ_U ≅ Ri_! Ri^! M ⟶ Ri_! Ri^! (M ⊗ N)`, through
`M ≅ M ⊗ Λ_U ⟶ M ⊗ N`. -/
theorem supportedProduct_liftCounitOfRangeEqUniv_right (i : Z ⟶ U) (i₂ : Z₂ ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i₂]
    (hi : Set.range i₂.base = Set.univ)
    (h : Set.range i.base = Set.range i.base ∩ Set.range i₂.base)
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : 𝟙_ _ ⟶ N) :
    derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 _) (liftCounitOfRangeEqUniv Λ i₂ hi φ) ≫
        supportedProduct Λ i i₂ i h M N =
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U _).hom ≫
        (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map
          ((derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U M).inv ≫
            derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 M) φ)) := by
  have hS := isZero_leftDerivedUpperStar_derivedTensor_of_disjoint Λ i i₂ i h
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i
        ((R(i)^![Λ]).obj M))
    (isZero_leftDerivedUpperStar_of_disjoint_of_range_eq_univ (ModuleCat.{u + 1} Λ) i₂ hi
      (𝟙_ (DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))))
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_right)
  refine (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hS _).unique rfl ?_
  have hu : liftCounitOfRangeEqUniv Λ i₂ hi φ ≫
      (rightDerivedUpperShriekAdjunction Λ i₂).counit.app N = φ :=
    (existsUnique_comp_counit_of_range_eq_univ Λ i₂ hi φ).exists.choose_spec
  simp only [Category.assoc]
  erw [(rightDerivedUpperShriekAdjunction Λ i).counit.naturality]
  rw [Functor.id_map, supportedProduct_comp_counit, derivedTensorHom_comp, hu,
    ← derivedTensorHom_comp_derivedTensorRightUnitor_hom_assoc]
  erw [Iso.hom_inv_id_assoc]
  rw [derivedTensorHom_comp]
  simp only [Category.id_comp]
  exact congrArg (derivedTensorHom (ModuleCat.{u + 1} Λ) · φ) (Category.comp_id _)

/-- **The right unit law of the cup product with supports.** For a surjective closed immersion
`i₂`, a section `Δ` of the right unitor of `Λ_U` and the class `u` supported everywhere lifting
`φ : Λ_U ⟶ N`, the cup product `α ∪ u` is `α` followed by `M ≅ M ⊗ Λ_U ⟶ M ⊗ N`. -/
theorem cupWithSupports_liftCounitOfRangeEqUniv_right (i : Z ⟶ U) (i₂ : Z₂ ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i₂]
    (hi : Set.range i₂.base = Set.univ)
    (h : Set.range i.base = Set.range i.base ∩ Set.range i₂.base)
    {M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (Δ : 𝟙_ _ ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (𝟙_ _)).obj (𝟙_ _))
    (hΔ : Δ ≫ (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U _).hom = 𝟙 _) (φ : 𝟙_ _ ⟶ N)
    (α : 𝟙_ _ ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M)) :
    cupWithSupports Λ i i₂ i h Δ α (liftCounitOfRangeEqUniv Λ i₂ hi φ) =
      α ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map
        ((derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U M).inv ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 M) φ)) := by
  have e : derivedTensorHom (ModuleCat.{u + 1} Λ) α (liftCounitOfRangeEqUniv Λ i₂ hi φ) =
      derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 _) ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 _) (liftCounitOfRangeEqUniv Λ i₂ hi φ) := by
    rw [derivedTensorHom_comp, Category.id_comp, Category.comp_id]
  rw [cupWithSupports_eq, e, Category.assoc, supportedProduct_liftCounitOfRangeEqUniv_right,
    reassoc_of% derivedTensorHom_comp_derivedTensorRightUnitor_hom, reassoc_of% hΔ]

end Product

variable [HasKummerClass Λ]

section Tate

variable (U : Scheme.{u}) [HasInvertibleExponent Λ U]

omit [Finite Λ] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` (`AlgebraicGeometry.Etale.constantComplexDiagonal`) is a
section of the right unitor: it is a section of the left unitor, and `λ_𝟙 = ρ_𝟙`. -/
lemma constantComplexDiagonal_comp_derivedTensorRightUnitor_hom :
    constantComplexDiagonal Λ U ≫ (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U _).hom =
      𝟙 _ := by
  have h := constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom Λ U
  rw [derivedTensorRightUnitor_eq]
  erw [← unitors_equal]
  exact h

omit [Finite Λ] in
/-- The *right unit law* of the identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`) on `U`: through `Λ_U ≅ Λ_U(0)[0]`, the
identification `Λ(m)[2m] ⊗ Λ(0)[0] ≅ Λ(m)[2m]` is the right unitor. This is
`HasTateTwist.twistObjectAddIso_zero_right` together with the compatibility of the right unitor of
the derived tensor product with shifts (`DerivedCategory.rightUnitor_commShift_app`). -/
theorem shiftTateObjectAddIso_zero_right (m : ℤ) :
    (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U ((tateObject Λ U m)⟦2 * m⟧)).inv ≫
      derivedTensorHom _ (𝟙 _) ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫
        (shiftTateObjectAddIso Λ U m 0).hom =
    eqToHom (by rw [add_zero]) := by
  set Z := HasTateTwist.twistObjectZeroIso (Λ := Λ) U
  have hadd : (HasTateTwist.twistObjectAddIso U m 0).hom =
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (HasTateTwist.twistObject U m)).map Z.hom ≫
        (derivedTensorRightUnitor _ U _).hom ≫ eqToHom (by rw [add_zero]) := by
    rw [reassoc_of% (HasTateTwist.twistObjectAddIso_zero_right (Λ := Λ) U m), eqToHom_trans,
      eqToHom_refl, Category.comp_id]
  have e : derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 ((tateObject Λ U m)⟦2 * m⟧)) (Z.inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) =
      derivedTensorHom _ (𝟙 _) Z.inv ≫
        derivedTensorHom _ (𝟙 _) ((shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) := by
    rw [derivedTensorHom_comp, Category.comp_id]
  rw [e]
  simp only [shiftTateObjectAddIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Category.assoc]
  erw [reassoc_of% derivedTensorHom_shiftFunctorZero'_inv_comp_derivedTensorShiftIso_hom_right]
  rw [eqToHom_comp_shift_map_of_eq_assoc _ (show 2 * m = 2 * m + 2 * 0 by ring), hadd,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [← derivedTensor_obj_map_comp_flip_commShiftIso_hom_app_assoc]
  rw [derivedTensorHom_id_left]
  erw [← Functor.map_comp_assoc]
  rw [Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% derivedTensorRightUnitor_commShift]
  rw [Iso.inv_hom_id_assoc]
  simp [eqToHom_map]

end Tate

omit [HasKummerClass Λ] in
variable {Λ} in
/-- Restriction of supports across an identification `L' = L''` of target coefficients. -/
lemma restrictSupportedClass_trans_eqToIso {U U' Z Z' : Scheme.{u}} (e : U' ⟶ U) (i : Z ⟶ U)
    (i' : Z' ⟶ U') [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z)
    (hg : IsPullback g i' i e)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' L'' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') (hL : L' = L'')
    (γ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    restrictSupportedClass Λ e i i' g hg σ (τ ≪≫ eqToIso hL) γ =
      restrictSupportedClass Λ e i i' g hg σ τ γ ≫ eqToHom (by rw [hL]) := by
  subst hL
  simp

omit [HasKummerClass Λ] in
variable {Λ} in
/-- Restriction of supports across an equation `s = t` of the sets of functions cutting out the
closed subscheme `V(s) = V(t)`. -/
lemma restrictSupportedClass_comp_eqToHom_zeroLocusSubschemeι {U U' : Scheme.{u}} (e : U' ⟶ U)
    {s t : Set Γ(U, ⊤)} (hst : s = t) {s' : Set Γ(U', ⊤)}
    (g : U'.zeroLocusSubscheme s' ⟶ U.zeroLocusSubscheme t)
    (hg : IsPullback g (U'.zeroLocusSubschemeι s') (U.zeroLocusSubschemeι t) e)
    (g' : U'.zeroLocusSubscheme s' ⟶ U.zeroLocusSubscheme s)
    (hg' : IsPullback g' (U'.zeroLocusSubschemeι s') (U.zeroLocusSubschemeι s) e)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : K ⟶ (R(U.zeroLocusSubschemeι s)_![ModuleCat.{u + 1} Λ]).obj
      ((R(U.zeroLocusSubschemeι s)^![Λ]).obj L)) :
    restrictSupportedClass Λ e _ _ g hg σ τ (γ ≫ eqToHom (by rw [hst])) =
      restrictSupportedClass Λ e _ _ g' hg' σ τ γ := by
  subst hst
  obtain rfl : g = g' := (cancel_mono (U.zeroLocusSubschemeι s)).1 (hg.w.trans hg'.w.symm)
  simp

section Kummer

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U]

/-- **The right unit law.** The cup product with the empty product of Kummer boundaries (the unit
class supported everywhere) on the right is the identity. -/
theorem cupWithSupportsTateObject_kummerBoundaryProduct_zero_right {Z : Scheme.{u}}
    (f : Fin 0 → Γ(U, ⊤)) (i : Z ⟶ U) [IsClosedImmersion i]
    (h : Set.range i.base =
      Set.range i.base ∩ Set.range (U.zeroLocusSubschemeι (Set.range f)).base) {m : ℤ}
    (α : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧))) :
    cupWithSupportsTateObject Λ i (U.zeroLocusSubschemeι (Set.range f)) i h α
        (kummerBoundaryProduct Λ f) =
      α ≫ eqToHom (by rw [Nat.cast_zero, add_zero]) := by
  have hunit :
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) U ((tateObject Λ U m)⟦2 * m⟧)).inv ≫
      derivedTensorHom _ (𝟙 _) ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫
        (shiftTateObjectAddIso Λ U m ((0 : ℕ) : ℤ)).hom =
      eqToHom (by rw [Nat.cast_zero, add_zero]) :=
    shiftTateObjectAddIso_zero_right Λ U m
  rw [kummerBoundaryProduct, cupWithSupportsTateObject,
    cupWithSupports_liftCounitOfRangeEqUniv_right Λ i _ _ h
      (constantComplexDiagonal Λ U)
      (constantComplexDiagonal_comp_derivedTensorRightUnitor_hom Λ U),
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, hunit]
  simp only [eqToHom_map]

/-- **The product of a single Kummer boundary.** For a one-element tuple `(f₁)`, the product of
Kummer boundaries `∂κ(f₁) ∪ 1` is the Kummer boundary `∂κ(f₁)`, read as a class with
coefficients `Λ(1)[2]` and supports in `V(f₁)`. -/
theorem kummerBoundaryProduct_one (f : Fin 1 → Γ(U, ⊤)) :
    kummerBoundaryProduct Λ f =
      shiftSupportedClass Λ _ 2 (kummerBoundary Λ (f 0)) ≫
        (eqToHom (by norm_num) :
          (R(U.zeroLocusSubschemeι {f 0})_![ModuleCat.{u + 1} Λ]).obj
              ((R(U.zeroLocusSubschemeι {f 0})^![Λ]).obj ((tateObject Λ U 1)⟦(2 : ℤ)⟧)) ⟶
            (R(U.zeroLocusSubschemeι {f 0})_![ModuleCat.{u + 1} Λ]).obj
              ((R(U.zeroLocusSubschemeι {f 0})^![Λ]).obj
                ((tateObject Λ U ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))) ≫
        eqToHom (by rw [Set.range_unique, Fin.default_eq_zero]) := by
  have hs : Set.range f = {f 0} := by rw [Set.range_unique, Fin.default_eq_zero]
  have h' : Set.range (U.zeroLocusSubschemeι {f 0}).base = Set.range
      (U.zeroLocusSubschemeι {f 0}).base ∩
        Set.range (U.zeroLocusSubschemeι (Set.range (Fin.tail f))).base := by
    rw [Set.range_eq_empty (Fin.tail f), range_zeroLocusSubschemeι_empty, Set.inter_univ]
  rw [kummerBoundaryProduct, cupWithSupportsTateObject_zeroLocusSubschemeι_congr Λ _ _ hs _ h',
    cupWithSupportsTateObject_kummerBoundaryProduct_zero_right Λ (Fin.tail f) _ h']
  simp only [Category.assoc, eqToHom_trans]

end Kummer

/-- **Base change of the product of a single Kummer boundary.** For `e : U' ⟶ U`, a one-element
tuple `(f₁)` on `U` and `x = e^* f₁`, restricting `∂κ(f₁) ∪ 1 ∈ H²_{V(f₁)}(U, Λ(1))` along `e`
gives the Kummer boundary `∂κ(x) ∈ H²_{V(x)}(U', Λ(1))`. -/
theorem restrictSupportedClass_kummerBoundaryProduct_one {U U' : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U'] (e : U' ⟶ U)
    (f : Fin 1 → Γ(U, ⊤)) (x : Γ(U', ⊤)) (hx : e.appTop (f 0) = x)
    (g : U'.zeroLocusSubscheme {x} ⟶ U.zeroLocusSubscheme (Set.range f))
    (hg : IsPullback g (U'.zeroLocusSubschemeι {x}) (U.zeroLocusSubschemeι (Set.range f)) e) :
    restrictSupportedClass Λ e _ _ g hg (leftDerivedUpperStarConstantComplexIso Λ e).inv
        (leftDerivedUpperStarTateShiftIso Λ e ((1 : ℕ) : ℤ) ≪≫ eqToIso (by norm_num))
        (kummerBoundaryProduct Λ f) =
      shiftSupportedClass Λ _ 2 (kummerBoundary Λ x) := by
  have hs : ({f 0} : Set Γ(U, ⊤)) = Set.range f := by
    rw [Set.range_unique, Fin.default_eq_zero]
  have hg' := isPullback_zeroLocusSubschemeι e {f 0} {x} (by rw [Set.image_singleton, hx])
  rw [kummerBoundaryProduct_one, ← Category.assoc,
    restrictSupportedClass_comp_eqToHom_zeroLocusSubschemeι e hs g hg
    _ hg', restrictSupportedClass_trans_eqToIso]
  erw [restrictSupportedClass_comp_eqToHom Λ e _ _ _ hg' (Nat.cast_one (R := ℤ)).symm]
  erw [restrictSupportedClass_shiftSupportedClass]
  rw [Category.assoc, eqToHom_trans]
  refine (Category.comp_id _).trans ?_
  exact congrArg (shiftSupportedClass Λ _ 2) (kummerBoundary_baseChange_of_eq Λ e (f 0) x hx _ hg')

end Etale

end AlgebraicGeometry
