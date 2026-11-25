/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapBaseChange

/-!
# Base change of the projective-line trace

Blueprint `det-sp-p1-trace`, clauses (1) and (2): the decomposition map
`(1, h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])` of the projective line `q : ℙ¹_S ⟶ S`
(`AlgebraicGeometry.Etale.projectiveLineDecompositionMap`) and the trace
`Tr_q : Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Λ_S` (`AlgebraicGeometry.Etale.projectiveLineTrace`) commute with
every base change `g : S' ⟶ S`, through the proper base change map
`Lg^* Rq_* ⟶ Rq'_* Lg'^*` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the canonical
identifications of the pulled back coefficients.

## The argument

The unit component of `(1, h)` commutes with base change by the compatibility of the base change
map with the units of the adjunctions. For the component `h`, the hyperplane class
`h = -c₁(𝒪(1))` is the class of the section at infinity with forgotten supports
(`AlgebraicGeometry.Etale.chartBoundaryClass_eq`), so it suffices to see that the class with
supports restricts to the class with supports of `ℙ¹_{S'}`
(`AlgebraicGeometry.Etale.restrictSupportedClass_chartBoundarySupportedClass_of_isPullback`).
Classes supported on the section at infinity are determined by their restrictions to the chart at
infinity (`AlgebraicGeometry.Etale.restrictSupportedClass_injective_of_isOpenImmersion`), where
the class with supports is the Kummer boundary of the coordinate
(`AlgebraicGeometry.Etale.restrictSupportedClass_chartBoundarySupportedClass`), which commutes
with base change (`AlgebraicGeometry.Etale.kummerBoundary_baseChange_of_eq`).

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineHyperplaneClass_baseChange`
- `AlgebraicGeometry.Etale.projectiveLineDecompositionMap_baseChange`
- `AlgebraicGeometry.Etale.projectiveLineTrace_baseChange`
- `AlgebraicGeometry.Etale.projectiveLineTrace_lowerShriek_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] HasInvertibleExponent.opens

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

section TateTwo

omit [Finite Λ] in
/-- The identifications `Lf^*(Λ(1)[2]) ≅ Λ(1)[2]`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwoIso`) are compatible
with composition, for a composite given up to an equality. -/
lemma leftDerivedUpperStarTateTwoIso_comp {X Y S : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ S] (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app
        ((tateObject Λ S 1)⟦(2 : ℤ)⟧) ≪≫
      (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateTwoIso Λ g) ≪≫
        leftDerivedUpperStarTateTwoIso Λ f = leftDerivedUpperStarTateTwoIso Λ fg := by
  ext
  have hc := NatTrans.shift_app_comm (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).hom
    (2 : ℤ) (tateObject Λ S 1)
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  simp only [leftDerivedUpperStarTateTwoIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, leftDerivedUpperStarTateObjectIso_comp f g fg h 1]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← reassoc_of% hc]

omit [Finite Λ] in
/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the identifications `Lf^*(Λ(1)[2]) ≅ Λ(1)[2]`. -/
lemma derivedSquareUpperStarIso_hom_app_tateTwo {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ X'] [HasInvertibleExponent Λ Y']
    (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app ((tateObject Λ Y 1)⟦(2 : ℤ)⟧) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ f).hom ≫
          (leftDerivedUpperStarTateTwoIso Λ g').hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ g).hom ≫
        (leftDerivedUpperStarTateTwoIso Λ f').hom := by
  have h₁ := leftDerivedUpperStarTateTwoIso_comp (Λ := Λ) g' f (g' ≫ f) rfl
  have h₂ := leftDerivedUpperStarTateTwoIso_comp (Λ := Λ) f' g (g' ≫ f) sq.w
  rw [← h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, ← h₃, Iso.inv_hom_id_app_assoc]

end TateTwo

section ChartBoundary

variable {X : Scheme.{u}} [HasInvertibleExponent Λ X] (V : X.Opens) (s : Γ(X, V))
  [IsClosedImmersion (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)]

variable (Λ) in
/-- **The class with supports of the zero locus of `s`, restricted to `V`, is the Kummer
boundary of `s`.** The restriction to the open `V` of the class with supports
`AlgebraicGeometry.Etale.chartBoundarySupportedClass` is `∂κ(s)`, read with coefficients
`Λ_V(1)[2]`. -/
theorem restrictSupportedClass_chartBoundarySupportedClass :
    restrictSupportedClass Λ V.ι _ _ (𝟙 _)
        (isPullback_id_comp_of_mono (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) V.ι)
        (leftDerivedUpperStarConstantComplexIso Λ V.ι).inv
        (leftDerivedUpperStarTateTwoIso Λ V.ι) (chartBoundarySupportedClass Λ V s) =
      shiftSupportedClass Λ _ 2 (kummerBoundary Λ (V.topIso.inv s)) := by
  apply (supportedClassMap_bijective Λ _ _).injective
  have h := map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map Λ
    (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) V.ι (tateObject Λ X 1)
    (leftDerivedUpperStarTateObjectIso V.ι 1) 2 (kummerBoundaryAdjoint Λ (V.topIso.inv s))
  rw [supportedClassMap_restrictSupportedClass]
  unfold chartBoundarySupportedClass leftDerivedUpperStarTateTwoIso
  have h' := congrArg ((leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv ≫ ·) h
  simp only at h'
  convert h' using 4
  rw [leftDerivedUpperStarConstantComplexIso_inv_comp_leftDerivedUpperStarId_hom_app_assoc]
  exact supportedClassMap_shiftSupportedClass_kummerBoundary Λ _

variable {X' : Scheme.{u}} [HasInvertibleExponent Λ X'] (e : X' ⟶ X) (V' : X'.Opens)
  (s' : Γ(X', V'))
  [IsClosedImmersion (V'.toScheme.zeroLocusSubschemeι {V'.topIso.inv s'} ≫ V'.ι)]
  (m : V'.toScheme ⟶ V.toScheme) (sq : IsPullback m V'.ι V.ι e)
  (gZ : V'.toScheme.zeroLocusSubscheme {V'.topIso.inv s'} ⟶
    V.toScheme.zeroLocusSubscheme {V.topIso.inv s})
  (hgZ : IsPullback gZ (V'.toScheme.zeroLocusSubschemeι {V'.topIso.inv s'})
    (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) m)

variable (Λ) in
/-- **Base change of the class with supports of the zero locus of a function on an open.** For
`e : X' ⟶ X`, opens `V ⊆ X` and `V' = e⁻¹(V)` and a function `s` on `V` pulling back to `s'` on
`V'`, the restriction along `e` of the class with supports of the zero locus of `s`
(`AlgebraicGeometry.Etale.chartBoundarySupportedClass`) is the class with supports of the zero
locus of `s'`. -/
theorem restrictSupportedClass_chartBoundarySupportedClass_of_isPullback
    (hs : m.appTop (V.topIso.inv s) = V'.topIso.inv s') :
    restrictSupportedClass Λ e _ _ gZ (hgZ.paste_vert sq)
        (leftDerivedUpperStarConstantComplexIso Λ e).inv
        (leftDerivedUpperStarTateTwoIso Λ e) (chartBoundarySupportedClass Λ V s) =
      chartBoundarySupportedClass Λ V' s' := by
  have hT : IsPullback (𝟙 _ ≫ gZ) (V'.toScheme.zeroLocusSubschemeι {V'.topIso.inv s'})
      (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι) (V'.ι ≫ e) :=
    (isPullback_id_comp_of_mono _ _).paste_horiz (hgZ.paste_vert sq)
  have hL := restrictSupportedClass_restrictSupportedClass Λ e V'.ι (V'.ι ≫ e) rfl _ _ _ gZ
    (hgZ.paste_vert sq) (𝟙 _) (isPullback_id_comp_of_mono _ _) _ hT
    (leftDerivedUpperStarConstantComplexIso Λ e).inv
    (leftDerivedUpperStarConstantComplexIso Λ V'.ι).inv (leftDerivedUpperStarTateTwoIso Λ e)
    (leftDerivedUpperStarTateTwoIso Λ V'.ι) (chartBoundarySupportedClass Λ V s)
  have hR := restrictSupportedClass_restrictSupportedClass Λ V.ι m (V'.ι ≫ e) sq.w.symm _ _ _
    (𝟙 _) (isPullback_id_comp_of_mono _ _) gZ hgZ _ hT
    (leftDerivedUpperStarConstantComplexIso Λ V.ι).inv
    (leftDerivedUpperStarConstantComplexIso Λ m).inv (leftDerivedUpperStarTateTwoIso Λ V.ι)
    (leftDerivedUpperStarTateTwoIso Λ m) (chartBoundarySupportedClass Λ V s)
  rw [leftDerivedUpperStarConstantComplexIso_inv_comp, leftDerivedUpperStarTateTwoIso_comp]
    at hL hR
  have hK : restrictSupportedClass Λ m _ _ gZ hgZ (leftDerivedUpperStarConstantComplexIso Λ m).inv
      (leftDerivedUpperStarTateTwoIso Λ m)
        (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (V.topIso.inv s))) =
      shiftSupportedClass Λ _ 2 (kummerBoundary Λ (V'.topIso.inv s')) := by
    rw [leftDerivedUpperStarTateTwoIso, restrictSupportedClass_shiftSupportedClass,
      kummerBoundary_baseChange_of_eq Λ m _ _ hs]
  apply restrictSupportedClass_injective_of_isOpenImmersion Λ _ V'.ι
    (leftDerivedUpperStarTateTwoIso Λ V'.ι)
  rw [← hL, restrictSupportedClass_chartBoundarySupportedClass, ← hK,
    ← restrictSupportedClass_chartBoundarySupportedClass, ← hR]

end ChartBoundary

section ProjectiveLine

variable {S S' : Scheme.{u}} [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ S']
  (g : S' ⟶ S)

variable (Λ) in
/-- **Base change of the hyperplane class.** The pullback of the hyperplane class
`h ∈ H²(ℙ¹_S, Λ(1))` (`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux`) along
`g' : ℙ¹_{S'} ⟶ ℙ¹_S`, read through `Λ_{ℙ¹_{S'}} ≅ Lg'^* Λ_{ℙ¹_S}` and
`Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]`, is the hyperplane class of `ℙ¹_{S'}`. -/
theorem projectiveLineHyperplaneClassAux_baseChange :
    (leftDerivedUpperStarConstantComplexIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).inv ≫
      (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)^*[ModuleCat.{u + 1} Λ])).map
        (projectiveLineHyperplaneClassAux Λ S) ≫
      (leftDerivedUpperStarTateTwoIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom =
    projectiveLineHyperplaneClassAux Λ S' := by
  have hV := ProjectiveSpace.map_preimage_standardOpen g (some (⟨0⟩ : ULift.{u} (Fin 1)))
  let mV := (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g).resLE
    (ProjectiveSpace.lineInfinityOpen S) (ProjectiveSpace.lineInfinityOpen S') hV.ge
  have sq : IsPullback mV (ProjectiveSpace.lineInfinityOpen S').ι
      (ProjectiveSpace.lineInfinityOpen S).ι (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hV])
  have hs : mV.appTop (ProjectiveSpace.lineInfinityCoord S) =
      ProjectiveSpace.lineInfinityCoord S' := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply,
      CommRingCat.comp_apply, ProjectiveSpace.lineInfinityCoord,
      ProjectiveSpace.lineInfinityCoord, Iso.inv_hom_id_apply, ProjectiveSpace.map_appLE_coordRatio]
  have hs' : mV.appTop '' {ProjectiveSpace.lineInfinityCoord S} =
      {ProjectiveSpace.lineInfinityCoord S'} := by
    rw [Set.image_singleton, hs]
  rw [projectiveLineHyperplaneClassAux, projectiveLineHyperplaneClassAux, chartBoundaryClass_eq,
    chartBoundaryClass_eq, ← restrictSupportedClass_chartBoundarySupportedClass_of_isPullback Λ
      _ _ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) _ _ _ sq _
      (Scheme.isPullback_zeroLocusSubschemeι mV _ _ hs') hs,
    restrictSupportedClass_comp_counit]

variable (Λ) in
/-- **Base change of the hyperplane class** `h = c₁(𝒪(1))` of the notes
(`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`): the negative of the auxiliary statement
`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux_baseChange`. -/
theorem projectiveLineHyperplaneClass_baseChange :
    (leftDerivedUpperStarConstantComplexIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).inv ≫
      (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)^*[ModuleCat.{u + 1} Λ])).map
        (projectiveLineHyperplaneClass Λ S) ≫
      (leftDerivedUpperStarTateTwoIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom =
    projectiveLineHyperplaneClass Λ S' := by
  have := projectiveLineHyperplaneClassAux_baseChange Λ g
  simp only [projectiveLineHyperplaneClass, Functor.map_neg, Preadditive.comp_neg,
    Preadditive.neg_comp, neg_inj] at this ⊢
  exact this

variable (Λ) in
/-- **Base change of the auxiliary decomposition map**. Let `g' : ℙ¹_{S'} ⟶ ℙ¹_S` be the base
change of `g : S' ⟶ S`. The pullback along `g` of the auxiliary decomposition map
`(1, -h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`
(`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux`, with `-h = c₁(𝒪(-∞))`), followed by
the proper base change map `Lg^* Rq_* ⟶ Rq'_* Lg'^*` and `Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]`, is the
decomposition map of `ℙ¹_{S'}`, preceded by the identification
`Lg^*(Λ_S(1)[2] ⊕ Λ_S) ≅ Λ_{S'}(1)[2] ⊕ Λ_{S'}`. -/
theorem projectiveLineDecompositionMapAux_baseChange :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineDecompositionMapAux Λ S) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom =
      biprod.lift
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.fst ≫
            (leftDerivedUpperStarTateTwoIso Λ g).hom)
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.snd ≫
            (leftDerivedUpperStarConstantComplexIso Λ g).hom) ≫
        projectiveLineDecompositionMapAux Λ S' := by
  have sq := ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g
  have hU := leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap_comp sq.toCommSq
    (((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).commShiftIso
      (2 : ℤ)).hom.app _ ≫
        (leftDerivedUpperStarTateObjectIso (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) 1).hom⟦(2 : ℤ)⟧')
    (((L(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))^*[ModuleCat.{u + 1} Λ])).commShiftIso
      (2 : ℤ)).hom.app _ ≫
        (leftDerivedUpperStarTateObjectIso (ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S') 1).hom⟦2⟧')
    (leftDerivedUpperStarTateTwoIso Λ g).hom
    (leftDerivedUpperStarTateTwoIso Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom
    (derivedSquareUpperStarIso_hom_app_tateTwo sq.toCommSq)
  have hC := leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap_comp sq.toCommSq
    ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
      projectiveLineHyperplaneClassAux Λ S)
    ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S')).hom ≫
      projectiveLineHyperplaneClassAux Λ S')
    (leftDerivedUpperStarConstantComplexIso Λ g).hom
    (leftDerivedUpperStarTateTwoIso Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom
    (by
      rw [← projectiveLineHyperplaneClassAux_baseChange Λ g, Functor.map_comp, Category.assoc,
        ← reassoc_of% (derivedSquareUpperStarIso_hom_app_constantComplex Λ sq.toCommSq),
        Iso.hom_inv_id_assoc])
  simp only [projectiveLineDecompositionMapAux, Adjunction.homEquiv_unit, biprod.desc_eq,
    Functor.map_add, Preadditive.add_comp]
  rw [Functor.map_comp (L((g)^*[ModuleCat.{u + 1} Λ])) biprod.fst, Category.assoc, hU,
    Functor.map_comp (L((g)^*[ModuleCat.{u + 1} Λ])) biprod.snd, Category.assoc, hC]
  simp only [Preadditive.comp_add, biprod.lift_fst_assoc, biprod.lift_snd_assoc, Category.assoc]

variable (Λ) in
/-- **Base change of the decomposition map.** Let `g' : ℙ¹_{S'} ⟶ ℙ¹_S` be the base change of
`g : S' ⟶ S`. The pullback along `g` of the decomposition map
`(1, h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`
(`AlgebraicGeometry.Etale.projectiveLineDecompositionMap`, with the hyperplane class `h = c₁(𝒪(1))`
of the notes), followed by the proper base change map `Lg^* Rq_* ⟶ Rq'_* Lg'^*` and
`Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]`, is the decomposition map of `ℙ¹_{S'}`, preceded by the identification
`Lg^*(Λ_S(1)[2] ⊕ Λ_S) ≅ Λ_{S'}(1)[2] ⊕ Λ_{S'}`. From the auxiliary statement
`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux_baseChange`, since the decomposition map
is the auxiliary one precomposed with `1 ⊕ (-1)`, which commutes with the identification. -/
theorem projectiveLineDecompositionMap_baseChange :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineDecompositionMap Λ S) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom =
      biprod.lift
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.fst ≫
            (leftDerivedUpperStarTateTwoIso Λ g).hom)
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.snd ≫
            (leftDerivedUpperStarConstantComplexIso Λ g).hom) ≫
        projectiveLineDecompositionMap Λ S' := by
  have h := projectiveLineDecompositionMapAux_baseChange Λ g
  simp only [projectiveLineDecompositionMap, Functor.map_comp, Category.assoc]
  rw [h, ← Category.assoc, ← Category.assoc]
  congr 1
  ext
  · simp only [Category.assoc, biprod.lift_fst, ← Functor.map_comp_assoc, biprod.map_fst,
      Category.comp_id]
  · simp only [Category.assoc, biprod.lift_snd, ← Functor.map_comp_assoc, biprod.map_snd,
      Preadditive.comp_neg, Category.comp_id, Functor.map_neg, Preadditive.neg_comp]

variable (Λ) in
/-- **Base change of the auxiliary trace.** For
`g : S' ⟶ S` with base change `g' : ℙ¹_{S'} ⟶ ℙ¹_S`, the pullback along `g` of the trace
`Tr_q : Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Λ_S` (`AlgebraicGeometry.Etale.projectiveLineTraceAux`) is the
proper base change map `Lg^* Rq_* ⟶ Rq'_* Lg'^*`, followed by `Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]`, the
trace of `ℙ¹_{S'}` and `Λ_{S'} ≅ Lg^* Λ_S`. -/
theorem projectiveLineTraceAux_baseChange [HasKummerClass.IsNormalized Λ] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineTraceAux Λ S) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom ≫
        projectiveLineTraceAux Λ S' ≫ (leftDerivedUpperStarConstantComplexIso Λ g).inv := by
  have := isIso_projectiveLineDecompositionMapAux Λ S
  have := isIso_projectiveLineDecompositionMapAux Λ S'
  have h := projectiveLineDecompositionMapAux_baseChange Λ g
  have h₂ : (L((g)^*[ModuleCat.{u + 1} Λ])).map (inv (projectiveLineDecompositionMapAux Λ S)) ≫
      biprod.lift
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.fst ≫
            (leftDerivedUpperStarTateTwoIso Λ g).hom)
          ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.snd ≫
            (leftDerivedUpperStarConstantComplexIso Λ g).hom) =
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom) ≫
        inv (projectiveLineDecompositionMapAux Λ S') := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← h, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_mono (leftDerivedUpperStarConstantComplexIso Λ g).hom, Category.assoc,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, projectiveLineTraceAux,
    projectiveLineTraceAux, Functor.map_comp, Category.assoc, ← biprod.lift_snd
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.fst ≫ (leftDerivedUpperStarTateTwoIso Λ g).hom)
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map biprod.snd ≫
        (leftDerivedUpperStarConstantComplexIso Λ g).hom), reassoc_of% h₂]

variable (Λ) in
/-- **Base change of the trace**. For
`g : S' ⟶ S` with base change `g' : ℙ¹_{S'} ⟶ ℙ¹_S`, the pullback along `g` of the trace
`Tr_q : Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Λ_S` (`AlgebraicGeometry.Etale.projectiveLineTrace`) is the
proper base change map `Lg^* Rq_* ⟶ Rq'_* Lg'^*`, followed by `Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]`, the
trace of `ℙ¹_{S'}` and `Λ_{S'} ≅ Lg^* Λ_S`. From the auxiliary statement
`AlgebraicGeometry.Etale.projectiveLineTraceAux_baseChange` by `Tr_q = -Tr_q^{aux}`. -/
theorem projectiveLineTrace_baseChange [HasKummerClass.IsNormalized Λ] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineTrace Λ S) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom ≫
        projectiveLineTrace Λ S' ≫ (leftDerivedUpperStarConstantComplexIso Λ g).inv := by
  rw [projectiveLineTrace_eq_neg, projectiveLineTrace_eq_neg, Functor.map_neg,
    projectiveLineTraceAux_baseChange]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
variable (Λ) in
/-- **Base change of the trace on the compactly supported direct image.** The trace of
`ℙ¹_S` read on `Rq_! ≅ Rq_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`)
commutes with base change through the compactly supported base change map
`Ex_! : Lg^* Rq_! ⟶ Rq'_! Lg'^*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`):
`Rq_! ≅ Rq_*` intertwines `Ex_!` with the proper base change map
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso`). -/
theorem projectiveLineTrace_lowerShriek_baseChange [HasKummerClass.IsNormalized Λ] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
          (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom.app
            ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
          projectiveLineTrace Λ S) =
      (rightDerivedLowerShriekBaseChangeMap Λ
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)).app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≫
        (R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ]).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
          (ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S')).hom.app
            ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1)⟦(2 : ℤ)⟧) ≫
        projectiveLineTrace Λ S' ≫ (leftDerivedUpperStarConstantComplexIso Λ g).inv := by
  rw [Functor.map_comp, projectiveLineTrace_baseChange Λ g,
    ← rightDerivedLowerShriekBaseChangeMap_app_comp_lowerStarIso_assoc,
    NatTrans.naturality_assoc]

end ProjectiveLine

end Etale

end AlgebraicGeometry
