/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.LowerShriekTraceCounitBaseChange

/-!
# Base change of the section invariant isomorphism

For a cartesian square `eB ≫ s = s' ≫ eV` of closed immersions `s : B ⟶ V`, `s' : B' ⟶ V'`, the
isomorphism `Ls^* ω ≅ Ls^* T` built from `Rs^! T ≅ Λ_B` and `Rs^! ω ≅ Λ_B`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`, the tensor maps
`Rs^! M ⊗ Ls^* N ⟶ Rs^!(M ⊗ N)`, the symmetry and the unitors of `⊗ᴸ`) is compatible with base
change along `eB`, `eV`: given identifications `vω : LeV^* ω ≅ ω'`, `vT : LeV^* T ≅ T'` under
which the isomorphisms `Rs^! T ≅ Λ_B`, `Rs^! ω ≅ Λ_B` correspond to `Rs'^! T' ≅ Λ_{B'}`,
`Rs'^! ω' ≅ Λ_{B'}` through the exceptional base change
`LeB^* Rs^! ⟶ Rs'^! LeV^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`), the
two section invariant isomorphisms correspond through `LeB^* Ls^* ≅ Ls'^* LeV^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_baseChange`).

This is the geometric form of the hypothesis
`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso` of the change
of coefficients. The inputs are the base change of the tensor maps
(`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv`, with the compatibility of the
projection formula with compact-support base change
`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`), the
compatibility of the tensor comparison of the derived pullback with the symmetry
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison`)
and with the left unitor
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product and of the tensor maps of `R^!`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange`, whose
-- instantiation of the base change of the tensor maps is repeated below.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {V B V' B' : Scheme.{u}} {s : B ⟶ V} [IsClosedImmersion s] {s' : B' ⟶ V'} [IsClosedImmersion s']
  {eV : V' ⟶ V} {eB : B' ⟶ B} (hsq : IsPullback eB s' s eV)

section TensorMap

/-- **Base change of the tensor maps `Rs^! M ⊗ Ls^* N ⟶ Rs^!(M ⊗ N)`.** The instance of
`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv` for the square `eB ≫ s = s' ≫ eV`,
followed by identifications `vM : LeV^* M ≅ M'`, `vN : LeV^* N ≅ N'`. -/
lemma leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap_baseChange
    {M N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M' N' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (vM : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj M ≅ M')
    (vN : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj N ≅ N') :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap s M N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (M ⊗ N) ≫
        (R(s')^![Λ]).map ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV M N).hom ≫
          vM.hom ▷ _ ≫ M' ◁ vN.hom) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app M ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq N ≫
        (R(s')^![Λ]).map vM.hom ▷ _ ≫
        _ ◁ (L((s')^*[ModuleCat.{u + 1} Λ])).map vN.hom ≫
        rightDerivedUpperShriekTensorMap s' M' N' := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hsq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ hsq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  have key : (L((eB)^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap s M N) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (M ⊗ N) ≫
        (R(s')^![Λ]).map (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV M N).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app M ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq N ≫
        rightDerivedUpperShriekTensorMap s' _ _ :=
    Adjunction.projectionTensorMap_mateEquiv
      (rightDerivedUpperShriekAdjunction Λ s) (rightDerivedUpperShriekAdjunction Λ s')
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) s).app M).app N)
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) s').app M).app N)
      (projectionMap_app_app_naturality_left s')
      (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB M M').hom)
      (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV N N').hom)
      (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left eV φ N'')
      (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq N)
      (rightDerivedLowerShriekBaseChangeMap Λ hsq)
      (inv (rightDerivedLowerShriekBaseChangeMap Λ hsq))
      (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N
  have hr : (R(s')^![Λ]).obj M' ◁ (L((s')^*[ModuleCat.{u + 1} Λ])).map vN.hom ≫
      rightDerivedUpperShriekTensorMap s' M' N' =
        rightDerivedUpperShriekTensorMap s' M' _ ≫ (R(s')^![Λ]).map (M' ◁ vN.hom) :=
    Adjunction.projectionTensorMap_naturality_right _ _
      (projectionMap_app_app_naturality_right s') M' vN.hom
  have hl : (R(s')^![Λ]).map vM.hom ▷ (L((s')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((eV)^*[ModuleCat.{u + 1} Λ])).obj N) ≫ rightDerivedUpperShriekTensorMap s' M' _ =
      rightDerivedUpperShriekTensorMap s' _ _ ≫ (R(s')^![Λ]).map (vM.hom ▷ _) :=
    Adjunction.projectionTensorMap_naturality_left _ _
      (projectionMap_app_app_naturality_left s') vM.hom _
  rw [Functor.map_comp, Functor.map_comp, reassoc_of% key, hr, reassoc_of% hl]
  rfl

end TensorMap

section Squares

variable (Λ)

/-- Base change of the symmetry `Rs^!(M ⊗ N) ≅ Rs^!(N ⊗ M)`, through the exceptional base
change and the tensor comparison of `LeV^*`. -/
lemma leftDerivedUpperStar_map_rightDerivedUpperShriek_map_braiding_baseChange
    {M N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M' N' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (vM : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj M ≅ M')
    (vN : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj N ≅ N') :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        ((R(s)^![Λ]).map (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (N ⊗ M) ≫
        (R(s')^![Λ]).map ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV N M).hom ≫
          vN.hom ▷ _ ≫ N' ◁ vM.hom) =
      (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (M ⊗ N) ≫
        (R(s')^![Λ]).map ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV M N).hom ≫
          vM.hom ▷ _ ≫ M' ◁ vN.hom) ≫
        (R(s')^![Λ]).map (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V' M' N').hom := by
  have hn := (rightDerivedUpperShriekBaseChangeMap Λ hsq).naturality
    (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  have hb : (L((eV)^*[ModuleCat.{u + 1} Λ])).map
      (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV N M).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV M N).hom ≫
        (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V' _ _).hom :=
    leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison eV M N
  have h1 := derivedTensorBraidingIso_hom_naturality_right
    ((L((eV)^*[ModuleCat.{u + 1} Λ])).obj M) vN.hom
  have h2 := derivedTensorBraidingIso_hom_naturality_left vM.hom N'
  rw [derivedTensor_obj_map, derivedTensor_map_app] at h1
  rw [derivedTensor_map_app, derivedTensor_obj_map] at h2
  have hn' : (L((eB)^*[ModuleCat.{u + 1} Λ])).map
      ((R(s)^![Λ]).map (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (N ⊗ M) =
      (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (M ⊗ N) ≫
        (R(s')^![Λ]).map ((L((eV)^*[ModuleCat.{u + 1} Λ])).map
          (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom) := hn
  have hin : (L((eV)^*[ModuleCat.{u + 1} Λ])).map
      (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V M N).hom ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV N M).hom ≫
        vN.hom ▷ _ ≫ N' ◁ vM.hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV M N).hom ≫
        vM.hom ▷ _ ≫ M' ◁ vN.hom ≫
        (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) V' M' N').hom := by
    rw [reassoc_of% hb, ← reassoc_of% h1, ← h2, whisker_exchange_assoc]
  rw [reassoc_of% hn', ← Functor.map_comp, hin, ← Functor.map_comp, Category.assoc,
    Category.assoc]

omit [Finite Λ] [IsClosedImmersion s] [IsClosedImmersion s'] in
/-- Base change of the inverse of the left unitor `Λ_B ⊗ Ls^* K ≅ Ls^* K`. -/
lemma leftDerivedUpperStar_map_derivedTensorLeftUnitor_inv_baseChange
    {K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K') :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) B
          ((L((s)^*[ModuleCat.{u + 1} Λ])).obj K)).inv ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB (constantComplex Λ B) _).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ ≫
        _ ◁ (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
          (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom) =
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) B' _).inv := by
  let _ := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) eB
  have hη : (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      Functor.OplaxMonoidal.η (L((eB)^*[ModuleCat.{u + 1} Λ])) := rfl
  have h := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ) eB
    ((L((s)^*[ModuleCat.{u + 1} Λ])).obj K)
  rw [derivedTensor_map_app] at h
  have hn := (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) B').hom.naturality
    (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
      (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom)
  simp only [derivedTensorLeftUnitorNatIso, NatIso.ofComponents_hom_app, Functor.id_map,
    derivedTensor_obj_map] at hn
  unfold constantComplex
  rw [hη, ← cancel_mono (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) B' _).hom]
  simp only [Category.assoc]
  rw [hn, Iso.inv_hom_id, Category.comp_id, ← reassoc_of% h, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

omit [Finite Λ] [IsClosedImmersion s] [IsClosedImmersion s'] in
/-- Base change of the left unitor `Λ_B ⊗ Ls^* K ≅ Ls^* K`. -/
lemma leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom_baseChange
    {K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K') :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) B
          ((L((s)^*[ModuleCat.{u + 1} Λ])).obj K)).hom ≫
        derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB (constantComplex Λ B) _).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ ≫
        _ ◁ (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
          (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) B' _).hom := by
  let _ := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) eB
  have hη : (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      Functor.OplaxMonoidal.η (L((eB)^*[ModuleCat.{u + 1} Λ])) := rfl
  have h := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ) eB
    ((L((s)^*[ModuleCat.{u + 1} Λ])).obj K)
  rw [derivedTensor_map_app] at h
  have hn := (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) B').hom.naturality
    (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq K ≫
      (L((s')^*[ModuleCat.{u + 1} Λ])).map v.hom)
  simp only [derivedTensorLeftUnitorNatIso, NatIso.ofComponents_hom_app, Functor.id_map,
    derivedTensor_obj_map] at hn
  unfold constantComplex
  rw [hη, h, hn]
  simp only [Category.assoc]

variable {X T : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  {X' T' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  (vX : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj X ≅ X')
  (vT : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj T ≅ T')

/-- Base change of `θ⁻¹ ▷ Ls^* X : Λ_B ⊗ Ls^* X ⟶ Rs^! T ⊗ Ls^* X`, for `θ : Rs^! T ≅ Λ_B`
corresponding to `θ' : Rs'^! T' ≅ Λ_{B'}`. -/
lemma leftDerivedUpperStar_map_whiskerRight_inv_baseChange
    (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B)
    (θ' : (R(s')^![Λ]).obj T' ≅ constantComplex Λ B')
    (hθ : (L((eB)^*[ModuleCat.{u + 1} Λ])).map θ.hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ≫ (R(s')^![Λ]).map vT.hom) ≫ θ'.hom) :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (((derivedTensor (ModuleCat.{u + 1} Λ) B).map θ.inv).app
          ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq X ≫
        (R(s')^![Λ]).map vT.hom ▷ _ ≫
        _ ◁ (L((s')^*[ModuleCat.{u + 1} Λ])).map vX.hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB (constantComplex Λ B) _).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ ≫
        _ ◁ (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq X ≫
          (L((s')^*[ModuleCat.{u + 1} Λ])).map vX.hom) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) B').map θ'.inv).app
          ((L((s')^*[ModuleCat.{u + 1} Λ])).obj X') := by
  have hθ' : (leftDerivedUpperStarConstantComplexIso Λ eB).hom ≫ θ'.inv =
      (L((eB)^*[ModuleCat.{u + 1} Λ])).map θ.inv ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ≫ (R(s')^![Λ]).map vT.hom := by
    rw [← cancel_epi ((L((eB)^*[ModuleCat.{u + 1} Λ])).map θ.hom), reassoc_of% hθ,
      ← Functor.map_comp_assoc, Iso.hom_inv_id, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
  have hθw : (L((eB)^*[ModuleCat.{u + 1} Λ])).map θ.inv ▷
        ((L((eB)^*[ModuleCat.{u + 1} Λ])).obj ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ▷ _ ≫
        (R(s')^![Λ]).map vT.hom ▷ _ =
      (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ ≫ θ'.inv ▷ _ := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, ← comp_whiskerRight, hθ']
  have hδ := leftDerivedUpperStarTensorIso_hom_naturality_left eB θ.inv
    ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)
  rw [derivedTensor_map_app, derivedTensor_map_app] at hδ
  rw [derivedTensor_map_app, derivedTensor_map_app, reassoc_of% hδ, whisker_exchange_assoc,
    reassoc_of% hθw, ← whiskerLeft_comp, whisker_exchange]

/-- Base change of `ε ▷ Ls^* X : Rs^! ω ⊗ Ls^* X ⟶ Λ_B ⊗ Ls^* X`, for `ε : Rs^! ω ≅ Λ_B`
corresponding to `ε' : Rs'^! ω' ≅ Λ_{B'}`. -/
lemma leftDerivedUpperStar_map_whiskerRight_hom_baseChange
    (ε : (R(s)^![Λ]).obj T ≅ constantComplex Λ B)
    (ε' : (R(s')^![Λ]).obj T' ≅ constantComplex Λ B')
    (hε : (L((eB)^*[ModuleCat.{u + 1} Λ])).map ε.hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ≫ (R(s')^![Λ]).map vT.hom) ≫ ε'.hom) :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (((derivedTensor (ModuleCat.{u + 1} Λ) B).map ε.hom).app
          ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB (constantComplex Λ B) _).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ ≫
        _ ◁ (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq X ≫
          (L((s')^*[ModuleCat.{u + 1} Λ])).map vX.hom) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq X ≫
        (R(s')^![Λ]).map vT.hom ▷ _ ≫
        _ ◁ (L((s')^*[ModuleCat.{u + 1} Λ])).map vX.hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) B').map ε'.hom).app
          ((L((s')^*[ModuleCat.{u + 1} Λ])).obj X') := by
  have hεw : (L((eB)^*[ModuleCat.{u + 1} Λ])).map ε.hom ▷
        ((L((eB)^*[ModuleCat.{u + 1} Λ])).obj ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)) ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom ▷ _ =
      (rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ▷ _ ≫
        (R(s')^![Λ]).map vT.hom ▷ _ ≫ ε'.hom ▷ _ := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, ← comp_whiskerRight, hε, Category.assoc]
  have hδ := leftDerivedUpperStarTensorIso_hom_naturality_left eB ε.hom
    ((L((s)^*[ModuleCat.{u + 1} Λ])).obj X)
  rw [derivedTensor_map_app, derivedTensor_map_app] at hδ
  rw [derivedTensor_map_app, derivedTensor_map_app, reassoc_of% hδ, reassoc_of% hεw,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, whisker_exchange]

end Squares

section Main

variable (Λ)

/-- **The section invariant isomorphism is compatible with base change.** For a cartesian
square `eB ≫ s = s' ≫ eV` of closed immersions, identifications `vω : LeV^* ω ≅ ω'`,
`vT : LeV^* T ≅ T'` of invertible objects, and isomorphisms `θ : Rs^! T ≅ Λ_B`,
`ε : Rs^! ω ≅ Λ_B`, `θ' : Rs'^! T' ≅ Λ_{B'}`, `ε' : Rs'^! ω' ≅ Λ_{B'}` corresponding under the
exceptional base change (`hθ`, `hε`), the isomorphisms `Ls^* ω ≅ Ls^* T` and
`Ls'^* ω' ≅ Ls'^* T'`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`) correspond
under `LeB^* Ls^* ≅ Ls'^* LeV^*`. This is the geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`. -/
theorem leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_baseChange
    {ω T : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {ω' T' : _root_.DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (vω : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj ω ≅ ω')
    (vT : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj T ≅ T')
    (hω : DerivedCategory.isInvertible Λ V ω) (hT : DerivedCategory.isInvertible Λ V T)
    (hω' : DerivedCategory.isInvertible Λ V' ω') (hT' : DerivedCategory.isInvertible Λ V' T')
    (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B) (ε : (R(s)^![Λ]).obj ω ≅ constantComplex Λ B)
    (θ' : (R(s')^![Λ]).obj T' ≅ constantComplex Λ B')
    (ε' : (R(s')^![Λ]).obj ω' ≅ constantComplex Λ B')
    (hθ : (L((eB)^*[ModuleCat.{u + 1} Λ])).map θ.hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app T ≫ (R(s')^![Λ]).map vT.hom) ≫ θ'.hom)
    (hε : (L((eB)^*[ModuleCat.{u + 1} Λ])).map ε.hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app ω ≫ (R(s')^![Λ]).map vω.hom) ≫ ε'.hom) :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s hω hT θ ε).hom ≫
        derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq T ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map vT.hom =
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq ω ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map vω.hom ≫
        (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s' hω' hT' θ' ε').hom := by
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s) T ((isInvertible_iff_exists_derivedTensor _).2 hω)
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s) ω ((isInvertible_iff_exists_derivedTensor _).2 hT)
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s') T' ((isInvertible_iff_exists_derivedTensor _).2 hω')
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ s') ω' ((isInvertible_iff_exists_derivedTensor _).2 hT')
  have S1 := leftDerivedUpperStar_map_derivedTensorLeftUnitor_inv_baseChange Λ hsq vω
  have S2 := leftDerivedUpperStar_map_whiskerRight_inv_baseChange Λ hsq vω vT θ θ' hθ
  have S3 := leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap_baseChange hsq vT vω
  have S4 := leftDerivedUpperStar_map_rightDerivedUpperShriek_map_braiding_baseChange Λ hsq vT vω
  have S5' := leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap_baseChange hsq vω vT
  have S5 : (L((eB)^*[ModuleCat.{u + 1} Λ])).map (inv (rightDerivedUpperShriekTensorMap s ω T)) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eB _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hsq).app ω ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq T ≫
        (R(s')^![Λ]).map vω.hom ▷ _ ≫
        _ ◁ (L((s')^*[ModuleCat.{u + 1} Λ])).map vT.hom =
      (rightDerivedUpperShriekBaseChangeMap Λ hsq).app (ω ⊗ T) ≫
        (R(s')^![Λ]).map ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) eV ω T).hom ≫
          vω.hom ▷ _ ≫ ω' ◁ vT.hom) ≫
        inv (rightDerivedUpperShriekTensorMap s' ω' T') := by
    rw [Functor.map_inv, IsIso.inv_comp_eq,
      ← cancel_mono (rightDerivedUpperShriekTensorMap s' ω' T')]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact S5'.symm
  have S6 := leftDerivedUpperStar_map_whiskerRight_hom_baseChange Λ hsq vT vω ε ε' hε
  have S7 := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom_baseChange Λ hsq vT
  simp only [leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
  rw [S7, reassoc_of% S6, reassoc_of% S5, reassoc_of% S4, reassoc_of% S3, reassoc_of% S2,
    reassoc_of% S1]

end Main

end AlgebraicGeometry.Etale
