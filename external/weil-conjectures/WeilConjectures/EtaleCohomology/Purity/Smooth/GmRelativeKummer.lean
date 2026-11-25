/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerRelativeBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RankOneLocal

/-!
# The affine line and the punctured line over a base, with `Λ(1) = μₙ ⊗ Λ` coefficients

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible in `k`,
`Y` a separated `k`-scheme of finite type, `p : 𝔸¹_Y ⟶ Y` the projection, `j : G ⟶ 𝔸¹_Y` the
complement of the zero section and `π = j ≫ p`. With the Tate twist `Λ(1) = μₙ ⊗ Λ` and its
Kummer classes (`AlgebraicGeometry.Etale.hasKummerClass`) this file proves blueprint
`prop-pur-gm-relative-kummer`:

1. the unit `Λ_Y(1) ⟶ Rp_* Lp^* Λ_Y(1)` is an isomorphism
   (`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`);
2. the unit `Λ_Y(1) ⟶ Rπ_* Lπ^* Λ_Y(1)` is an isomorphism on `H⁰`
   (`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup`), and
   `R¹π_* Λ(1)` is free of rank one on the Kummer class `κ(t)` of the coordinate
   (`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint`);
3. `R^m π_* Λ(1) = 0` for `m ≥ 2`
   (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup`);
4. the base change maps of `Rp_* Λ(1)` are isomorphisms
   (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_affineLine`), and
   `κ(t)` pulls back to `κ(t')`
   (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass_coord`).

It also proves the global orientation `thm-pur-affine-line-orientation`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`), the
rank-one local calculation `example-closed-support`, with the `Λ`-linear isomorphism
`H²_Z(𝔸¹_Ω, Λ(1)) ≅ Λ` sending `∂κ(t)` to `1`
(`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv`), and the structure of the
exceptional inverse image of the zero section `lem-pur-gysin-structure`, with the `Λ`-linear
isomorphism `H²_Z(𝔸¹_Y, Λ(1)) ≅ Γ(Z, H⁰(Rs^!(Λ(1)[2])))`
(`AlgebraicGeometry.Etale.supportCohomologyLinearEquivΓHomologyZero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] neZero_ringChar_of_finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The Kummer class of the coordinate of `𝔾_{m,Ω}` is free of rank one over every
algebraically closed field `Ω` (`AlgebraicGeometry.Etale.bijective_smul_kummerClassOf`), in the
form of the hypothesis of the relative statements. -/
theorem kummerClass_coord_smul_eq_zero (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [HasInvertibleExponent Λ (Spec (.of Ω))] (G' : Scheme.{u})
    (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))) [IsOpenImmersion j']
    (hj' : Set.range j'.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).base)ᶜ)
    [HasInvertibleExponent Λ G'] (c : Λ)
    (hc : c • kummerClass Λ (AffineSpace.unitLineCoord j' hj') = 0) : c = 0 :=
  (bijective_smul_kummerClassOf Λ j' hj').1 (show c • kummerClassOf G' Λ _ = (0 : Λ) • _ by
    rw [zero_smul]
    exact hc)

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY] [HasInvertibleExponent Λ Y]

include aY in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (1)).

The unit `Λ_Y(1) ⟶ Rp_* Lp^* Λ_Y(1) = Rp_* Λ_{𝔸¹_Y}(1)` of the projection `p : 𝔸¹_Y ⟶ Y` is an
isomorphism; with `AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine` for the
untwisted unit. With the latter this is clause (a) of the subsection statement
`sk-prop-a1-kummer`. -/
theorem isIso_unit_tateObject_affineLine :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1)) := by
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  exact isIso_unit_affineLine_of_cohomology Λ aY (isZero_cohomology_affineLine Λ (k := k))
    (nonempty_iso_cohomology_zero_affineLine Λ (k := k)).some
    (boundedConstructibleFiniteTor_tateObject Λ Y 1) eTY hLT

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)

include aY hj in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (2), degree zero).

For the complement `j : G ⟶ 𝔸¹_Y` of the zero section and `π = j ≫ p`, the unit
`Λ_Y(1) ⟶ Rπ_* Lπ^* Λ_Y(1)` is an isomorphism on `H⁰`: `R⁰π_* Λ(1) = Λ_Y(1)`. This is the
first half of clause (b) of the subsection statement `sk-prop-a1-kummer`: `R⁰π_* Λ(1) ≅ Λ_Y(1)`,
the pullback `p^*` followed by restriction along `j` being an isomorphism onto it. -/
theorem isIso_homology_zero_unit_tateObject_multiplicativeGroup :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  exact isIso_homology_zero_unit_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj
    (boundedConstructibleFiniteTor_tateObject Λ Y 1) eTY hLT

include aY in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (2), degree one).

`R¹π_* Λ(1)` is free of rank one on the Kummer class `κ(t)` of the coordinate: the morphism
`Λ_Y ⟶ R¹π_* Λ(1) = H⁰(Rπ_*(Λ(1)[1]))` adjoint to `κ(t) : Λ_G ⟶ Λ_G(1)[1]` is an
isomorphism. This is the second half of clause (b) of `sk-prop-a1-kummer`. -/
theorem isIso_homology_zero_kummerClassAdjoint [HasInvertibleExponent Λ G] :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).homEquiv _ _
          ((leftDerivedUpperStarConstantComplexIso Λ (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).hom ≫
            kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  exact isIso_homology_zero_kummerClassAdjoint_of_cohomology Λ aY
    (kummerClass_coord_smul_eq_zero Λ) j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj _

include aY hj in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (3)).

`R^m π_* Λ(1) = 0` for `m ∉ {0, 1}`; in particular for `m ≥ 2`. This is clause (c) of
`sk-prop-a1-kummer` for the twist `Λ(1) = μₙ ⊗ Λ`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup
    [HasInvertibleExponent Λ G] (m : ℤ) (h₀ : m ≠ 0) (h₁ : m ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ G 1))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj
    (boundedConstructibleFiniteTor_tateObject Λ Y 1)
  exact (isZero_homology_biprodShift Λ _ (homology_props_of_iso_singleFunctor Λ eTY hLT).1 m h₀
    h₁).of_iso ((_root_.DerivedCategory.homologyFunctor _ m).mapIso
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarTateObjectIso (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1).symm ≪≫ e))

include aY in
/-- Blueprint `thm-pur-affine-line-orientation`: Global orientation and its normalization

For `Y` separated of finite type over the algebraically closed field `k` and the zero section
`s : V(t) ⟶ 𝔸¹_Y` (the zero locus of the coordinate, `V(t) ≅ Y`), the adjoint
`pur_s : Λ_{V(t)} ⟶ Rs^!(Λ(1)[2])` of the Kummer boundary `∂κ(t)` is an isomorphism: the
target is concentrated in degree zero, lisse of rank one, and generated by `∂κ(t)`, which the
localization triangle identifies with the generator `κ(t)` of `R¹π_* Λ(1)`
(`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint`). -/
theorem isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})
      (shiftSupportedClass Λ _ 2
        (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0))))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  exact isIso_supportedClassMap_kummerBoundary_coord_of_cohomology Λ aY
    (kummerClass_coord_smul_eq_zero Λ) (isZero_cohomology_affineLine Λ (k := k))
    (nonempty_iso_cohomology_zero_affineLine Λ (k := k)).some j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some

section RankOne

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]

/-- Post-composition with an isomorphism, as an additive equivalence of hom groups. -/
noncomputable def postcompAddEquiv {C : Type*} [Category C] [Preadditive C] {A B B' : C}
    (e : B ≅ B') : (A ⟶ B) ≃+ (A ⟶ B') :=
  AddEquiv.mk ((Iso.refl A).homCongr e) (fun f g ↦ by simp [Iso.homCongr])

/-- The zero locus `V(t)` of the coordinate of `𝔸¹_S` is connected when `S` is: it is isomorphic
to `S` through the zero section. -/
lemma connectedSpace_zeroLocusSubscheme_coord (S : Scheme.{u}) [ConnectedSpace S] :
    ConnectedSpace (𝔸(ULift.{u} (Fin 1); S).zeroLocusSubscheme
      {AffineSpace.coord S (ULift.up 0)}) :=
  (Homeomorph.connectedSpace_iff (Scheme.homeoOfIso
    (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) S
      (s := {AffineSpace.coord S (ULift.up 0)}) Set.range_unique))).1 inferInstance

/-- Blueprint `example-closed-support`: Rank-one local calculation (the
normalized isomorphism).

For an algebraically closed field `Ω` and the origin `Z = V(t) ⊂ 𝔸¹_Ω`, the `Λ`-linear
isomorphism `H²_Z(𝔸¹_Ω, Λ(1)) ≅ Hom(Λ_Z, Ri^!(Λ(1)[2])) ≅ Hom(Λ_Z, Λ_Z) ≅ Λ`: the first map is
`AlgebraicGeometry.Etale.supportCohomologyLinearEquiv`, the second is post-composition with the
inverse of the isomorphism `supportedClassMap (∂κ(t)) : Λ_Z ⟶ Ri^!(Λ(1)[2])`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`), and the
third is the inverse of `c ↦ c • 𝟙` (`AlgebraicGeometry.Etale.bijective_smul_id_constantComplex`,
`Z ≅ Spec Ω` being connected). It sends `∂κ(t)` to `1`
(`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv_kummerBoundary`). -/
noncomputable def supportCohomologyAffineLineLinearEquiv :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
          {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)}) 2).obj
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) 1) ≃ₗ[Λ] Λ :=
  haveI := isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed Λ (k := Ω)
    (𝟙 (Spec (.of Ω)))
  haveI := connectedSpace_zeroLocusSubscheme_coord (Spec (.of Ω))
  supportCohomologyLinearEquiv Λ _ _ 2 ≪≫ₗ
    Linear.homCongr Λ (Iso.refl _) (asIso (supportedClassMap Λ
      (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)})
      (shiftSupportedClass Λ _ 2
        (kummerBoundary Λ (AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)))))).symm ≪≫ₗ
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Λ _ (𝟙 (constantComplex Λ
      (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubscheme
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)}))))
      (by exact bijective_smul_id_constantComplex Λ)).symm

/-- Blueprint `example-closed-support`: Rank-one local calculation (the
normalization).

The isomorphism `AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv` sends the
boundary `∂κ(t)` of the Kummer class of the coordinate, read in `H²_Z(𝔸¹_Ω, Λ(1))` through
`AlgebraicGeometry.Etale.supportCohomologyAddEquiv` as its adjoint `Λ_Z ⟶ Ri^!(Λ(1)[2])`, to
`1`. -/
theorem supportCohomologyAffineLineLinearEquiv_kummerBoundary :
    supportCohomologyAffineLineLinearEquiv Λ Ω ((supportCohomologyAddEquiv Λ _ _ 2).symm
      (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)})
        (shiftSupportedClass Λ _ 2
          (kummerBoundary Λ (AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)))))) = 1 := by
  simp [supportCohomologyAffineLineLinearEquiv, LinearEquiv.symm_apply_eq, Linear.homCongr_apply]

/-- Blueprint `example-closed-support`: Rank-one local calculation

Let `Ω` be an algebraically closed field (the residue field of a geometric point), `Λ` a finite
ring whose exponent is invertible in `Ω`, `Z = V(t) ⊂ 𝔸¹_Ω` the origin and
`Λ(1) = μₙ ⊗ Λ`. The cohomology with supports `H^q_Z(𝔸¹_Ω, Λ(1))`
(`AlgebraicGeometry.Etale.derivedSupportCohomology`) vanishes for `q ≠ 2`, and the `Λ`-linear
isomorphism `H²_Z(𝔸¹_Ω, Λ(1)) ≅ Λ` of
`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv` sends the boundary `∂κ(t)` of
the Kummer class of the coordinate to `1`; equivalently, `c ↦ c • ∂κ(t)` is a bijection
`Λ ≅ H²_Z(𝔸¹_Ω, Λ(1))`, i.e. `∂κ(t)` is a free generator. Here `∂κ(t)` is read in `H²_Z` through
`H²_Z(𝔸¹_Ω, Λ(1)) ≅ Hom(Λ_Z, Ri^!(Λ(1)[2]))` (`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`)
as its adjoint `Λ_Z ⟶ Ri^!(Λ(1)[2])`. The proof is the global orientation over `Y = Spec Ω`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`): it
identifies `Ri^!(Λ(1)[2])` with `Λ_Z`, and `Z ≅ Spec Ω` has cohomology `Λ` in degree zero only. -/
theorem rankOne_supportCohomology_affineLine :
    (∀ q : ℤ, q ≠ 2 → Subsingleton ((derivedSupportCohomology (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)}) q).obj
          (tateObject Λ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) 1))) ∧
    supportCohomologyAffineLineLinearEquiv Λ Ω ((supportCohomologyAddEquiv Λ _ _ 2).symm
      (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)})
        (shiftSupportedClass Λ _ 2
          (kummerBoundary Λ (AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)))))) = 1 ∧
    Function.Bijective (fun c : Λ ↦ c • (supportCohomologyAddEquiv Λ _ _ 2).symm
      (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)})
        (shiftSupportedClass Λ _ 2
          (kummerBoundary Λ (AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)))))) := by
  let X := 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))
  let t : Γ(X, ⊤) := AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)
  let ι := X.zeroLocusSubschemeι {t}
  let Z := X.zeroLocusSubscheme {t}
  let L := tateObject Λ X 1
  let φ := supportedClassMap Λ ι (shiftSupportedClass Λ _ 2
    (kummerBoundary Λ t))
  have hφ : IsIso φ := isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed Λ
    (k := Ω) (𝟙 (Spec (.of Ω)))
  let eZ := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) (Spec (.of Ω))
    (s := {t}) Set.range_unique
  have : Projective (𝟙_ (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    projective_unit_of_iso Λ eZ.symm
  refine ⟨fun q hq ↦ ?_, supportCohomologyAffineLineLinearEquiv_kummerBoundary Λ Ω, ?_⟩
  · -- `Ri^!(Λ(1)[q]) ≅ Λ_Z[q - 2]`, and `Hom(Λ_Z, Λ_Z[n]) = 0` for `n ≠ 0`
    let I : (R(ι)^![Λ]).obj (L⟦q⟧) ≅ (constantComplex Λ Z)⟦q - 2⟧ :=
      (R(ι)^![Λ]).mapIso ((shiftFunctorAdd' _ 2 (q - 2) q (by ring)).app L) ≪≫
        ((R(ι)^![Λ]).commShiftIso (q - 2)).app (L⟦(2 : ℤ)⟧) ≪≫
        (shiftFunctor _ (q - 2)).mapIso (asIso φ).symm
    let u := constantComplexIsoSingleFunctor Λ Z
    have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((constantComplex Λ Z)⟦q - 2⟧)) :=
      (isZero_homology_constantComplex Λ Z (q - 2) (by omega)).of_iso
        (((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso (q - 2) 0 (q - 2)
          (by ring)).app _)
    have : Subsingleton (constantComplex Λ Z ⟶ (constantComplex Λ Z)⟦q - 2⟧) := by
      refine ⟨fun a b ↦ ?_⟩
      have h := (_root_.DerivedCategory.homSingleEquivOfProjective
        (𝟙_ (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) 0
          ((constantComplex Λ Z)⟦q - 2⟧)).injective (a₁ := u.inv ≫ a) (a₂ := u.inv ≫ b)
          (hz.eq_of_tgt _ _)
      simpa using congrArg (fun f ↦ u.hom ≫ f) h
    exact ((supportCohomologyAddEquiv Λ ι L q).trans
      (postcompAddEquiv I)).toEquiv.subsingleton
  · convert (supportCohomologyAffineLineLinearEquiv Λ Ω).symm.bijective using 1
    funext c
    rw [LinearEquiv.eq_symm_apply, map_smul,
      supportCohomologyAffineLineLinearEquiv_kummerBoundary, smul_eq_mul, mul_one]

end RankOne

section Gysin

include aY in
/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section (the identification of `Γ(Z, H⁰(R))`).

For the zero section `s : Z = V(t) ⟶ 𝔸¹_Y` and `R = Rs^!(Λ(1)[2])`, the `Λ`-linear isomorphism
`H²_Z(𝔸¹_Y, Λ(1)) ≅ Γ(Z, H⁰(R))`: a class, read as a morphism `g : Λ_Z ⟶ R` through
`AlgebraicGeometry.Etale.supportCohomologyLinearEquiv`, goes to the global section of `H⁰(R)`
which is the image of `1` under `H⁰(g) : Λ = H⁰(Λ_Z) ⟶ H⁰(R)`
(`AlgebraicGeometry.Etale.homConstantComplexLinearMapΓHomologyZero`). It is bijective since
`R ≅ Λ_Z` is concentrated in degree zero, through the adjoint of `∂κ(t)`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`). -/
noncomputable def supportCohomologyLinearEquivΓHomologyZero :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)}) 2).obj
          (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1) ≃ₗ[Λ]
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
          ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
            {AffineSpace.coord Y (ULift.up 0)})^![Λ]).obj
            ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧))) :=
  haveI := isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed Λ aY
  supportCohomologyLinearEquiv Λ _ _ 2 ≪≫ₗ
    LinearEquiv.ofBijective (homConstantComplexLinearMapΓHomologyZero Λ _)
      (bijective_homConstantComplexLinearMapΓHomologyZero Λ
        ((asIso (supportedClassMap Λ
          (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)})
          (shiftSupportedClass Λ _ 2
            (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0)))))).symm ≪≫
          constantComplexIsoSingleFunctor Λ _))

include aY in
@[simp]
lemma supportCohomologyLinearEquivΓHomologyZero_apply
    (x : (derivedSupportCohomology (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)}) 2).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)) :
    supportCohomologyLinearEquivΓHomologyZero Λ aY x =
      homConstantComplexLinearMapΓHomologyZero Λ _ (supportCohomologyAddEquiv Λ _ _ 2 x) := by
  unfold supportCohomologyLinearEquivΓHomologyZero
  rw [LinearEquiv.trans_apply]
  simp only [LinearEquiv.ofBijective_apply, supportCohomologyLinearEquiv_apply]

include aY in
/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section

Let `s : Z = V(t) ⟶ 𝔸¹_Y` be the zero section (`Z ≅ Y`) and `R = Rs^!(Λ(1)[2])`. Then:

1. `R` lies in `D^b_{ctf}(Z, Λ)`, is concentrated in degree zero, and its cohomology sheaf `H⁰(R)`
   is the constant sheaf `Λ` (lisse of rank one, generated by the boundary of `κ(t)`); indeed
   `R ≅ Λ_Z` through the adjoint of `∂κ(t)`
   (`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`);
2. `Γ(Z, H⁰(R)) ≅ H²_Z(𝔸¹_Y, Λ(1))` through
   `AlgebraicGeometry.Etale.supportCohomologyLinearEquivΓHomologyZero`, and this isomorphism sends
   the boundary `∂κ(t)` of the Kummer class of `t`, read in `H²_Z(𝔸¹_Y, Λ(1))` through
   `H²_Z(𝔸¹_Y, Λ(1)) ≅ Hom(Λ_Z, R)` (`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`) as the
   morphism `supportedClassMap (∂κ(t)) : Λ_Z ⟶ R`, to the global section of `H⁰(R)` determined
   by `supportedClassMap (∂κ(t))`: the image of `1` under
   `H⁰(supportedClassMap (∂κ(t))) : Λ = H⁰(Λ_Z) ⟶ H⁰(R)`. -/
theorem gysin_structure_zeroSection :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubscheme {AffineSpace.coord Y (ULift.up 0)})
        ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![Λ]).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧)) ∧
      (∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![Λ]).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧)))) ∧
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![Λ]).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧)) ≅
        (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ∧
      supportCohomologyLinearEquivΓHomologyZero Λ aY ((supportCohomologyAddEquiv Λ _ _ 2).symm
          (supportedClassMap Λ
            (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)})
            (shiftSupportedClass Λ _ 2
              (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0)))))) =
        ((constantSheafΓAdj _ (ModuleCat.{u + 1} Λ)).homEquiv _ _
          ((homologyZeroConstantComplexIso Λ _).inv ≫
            (_root_.DerivedCategory.homologyFunctor _ 0).map (supportedClassMap Λ
              (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)})
              (shiftSupportedClass Λ _ 2
                (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0))))))).hom 1 := by
  let X := 𝔸(ULift.{u} (Fin 1); Y)
  let t : Γ(X, ⊤) := AffineSpace.coord Y (ULift.up 0)
  let ι := X.zeroLocusSubschemeι {t}
  let Z := X.zeroLocusSubscheme {t}
  let L := tateObject Λ X 1
  let φ := supportedClassMap Λ ι (shiftSupportedClass Λ _ 2
    (kummerBoundary Λ t))
  have hφ : IsIso φ := isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed Λ aY
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))
  let P := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let eH : (H 0).obj ((R(ι)^![Λ]).obj (L⟦(2 : ℤ)⟧)) ≅ P :=
    (H 0).mapIso (asIso φ).symm ≪≫ homologyZeroConstantComplexIso Λ Z
  refine ⟨constructibleFiniteTor_of_iso Λ (asIso φ) (constructibleFiniteTor_constantComplex Λ Z),
    fun n hn ↦ (isZero_homology_constantComplex Λ Z n hn).of_iso ((H n).mapIso (asIso φ).symm),
    ⟨eH⟩, ?_⟩
  simp only [supportCohomologyLinearEquivΓHomologyZero_apply, AddEquiv.apply_symm_apply,
    homConstantComplexLinearMapΓHomologyZero_apply]

end Gysin

section BaseChange

variable {Y' : Scheme.{u}} (aY' : Y' ⟶ Spec (.of k)) [IsSeparated aY'] [LocallyOfFiniteType aY']
  [QuasiCompact aY'] [HasInvertibleExponent Λ Y'] (g : Y' ⟶ Y)
  {G' : Scheme.{u}} (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Y')) [IsOpenImmersion j']
  (hj' : Set.range j'.base =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y').base)ᶜ)

omit [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] [IsSeparated aY]
  [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY'] [LocallyOfFiniteType aY']
  [QuasiCompact aY'] [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Y'] in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (4), the Kummer class).

For `g : Y' ⟶ Y` with base change `g' : 𝔾_{m,Y'} ⟶ 𝔾_{m,Y}`, the pullback of the Kummer class
of the coordinate is the Kummer class of the coordinate: `Lg'^* κ(t) = κ(t')`, through
`Lg'^* Λ ≅ Λ` and `Lg'^* Λ(1) ≅ Λ(1)`. This is the compatibility of `κ(t)` with base change on
`Y` asserted in `sk-prop-a1-kummer`. -/
theorem leftDerivedUpperStar_map_kummerClass_coord [HasInvertibleExponent Λ G]
    [HasInvertibleExponent Λ G'] :
    (L((AffineSpace.complementMap g j j' hj hj')^*[ModuleCat.{u + 1} Λ])).map
        (kummerClass Λ (AffineSpace.unitLineCoord j hj)) ≫
      ((L((AffineSpace.complementMap g j j' hj hj')^*[ModuleCat.{u + 1} Λ])).commShiftIso
        (1 : ℤ)).hom.app (tateObject Λ G 1) ≫
      (leftDerivedUpperStarTateObjectIso (AffineSpace.complementMap g j j' hj hj')
        1).hom⟦(1 : ℤ)⟧' =
    (leftDerivedUpperStarConstantComplexIso Λ (AffineSpace.complementMap g j j' hj hj')).hom ≫
      kummerClass Λ (AffineSpace.unitLineCoord j' hj') := by
  rw [leftDerivedUpperStar_map_kummerClass,
    units_map_unitLineCoord g j hj j' hj' _ (AffineSpace.complementMap_comp g j j' hj hj')]

include aY aY' in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (4), the affine line).

For `g : Y' ⟶ Y`, the derived base change map `Lg^* Rp_* Λ(1) ⟶ Rp'_* Λ(1)` of the projections
`p : 𝔸¹_Y ⟶ Y` and `p' : 𝔸¹_{Y'} ⟶ Y'` is an isomorphism. With
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_constantComplex_affineLine` this is the
base change compatibility of clause (a) of `sk-prop-a1-kummer`. -/
theorem isIso_derivedBaseChangeMap_app_tateObject_affineLine :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)) :=
  isIso_derivedBaseChangeMap_app_tateObject_affineLine_of_cohomology Λ aY aY' g
    (isZero_cohomology_affineLine Λ (k := k))
    (nonempty_iso_cohomology_zero_affineLine Λ (k := k)).some

omit [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Y'] in
include aY aY' in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients (base change
of clause (a), untwisted).

For `g : Y' ⟶ Y`, the derived base change map `Lg^* Rp_* Λ ⟶ Rp'_* Λ` of the projections
`p : 𝔸¹_Y ⟶ Y` and `p' : 𝔸¹_{Y'} ⟶ Y'` is an isomorphism: it is compatible with the units
`Λ_Y ⟶ Rp_* Λ` and `Λ_{Y'} ⟶ Rp'_* Λ`, which are isomorphisms
(`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`). -/
theorem isIso_derivedBaseChangeMap_app_constantComplex_affineLine :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y))) := by
  let p := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let p' := 𝔸(ULift.{u} (Fin 1); Y') ↘ Y'
  let sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq
  let BC := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  let M := constantComplex Λ Y
  have hp : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M) :=
    isIso_unit_affineLine_of_cohomology Λ aY (isZero_cohomology_affineLine Λ (k := k))
      (cohomologyZeroConstantComplexIso Λ _) (constructibleFiniteTor_constantComplex Λ Y)
      (constantComplexIsoSingleFunctor Λ Y) (nonempty_sheafFiber_unit_iso Λ)
  have hp' : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p').unit.app
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
    (NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarConstantComplexIso Λ g)).2
      (isIso_unit_affineLine_of_cohomology Λ aY' (isZero_cohomology_affineLine Λ (k := k))
        (cohomologyZeroConstantComplexIso Λ _) (constructibleFiniteTor_constantComplex Λ Y')
        (constantComplexIsoSingleFunctor Λ Y') (nonempty_sheafFiber_unit_iso Λ))
  have hmate := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq M
  have h₁ : IsIso (BC.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
    have : IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M) ≫
          BC.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
      rw [hmate]
      infer_instance
    exact IsIso.of_isIso_comp_left ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M)) _
  exact (NatTrans.isIso_app_iff_of_iso BC (leftDerivedUpperStarConstantComplexIso Λ p)).1 h₁

set_option maxRecDepth 20000 in
-- the composites of derived functors between the derived categories of the two bases are large
include aY aY' in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (4), the punctured line).

For `g : Y' ⟶ Y` with base change `g' : 𝔾_{m,Y'} ⟶ 𝔾_{m,Y}`, the derived base change map
`Lg^* Rπ_* Λ(1) ⟶ Rπ'_* Lg'^* Λ(1)` is an isomorphism: both sides have cohomology only in degrees
zero and one, where the base change map is compatible with the units and with the Kummer
classes, which generate. This is the base change compatibility of clauses (b) and (c) of
`sk-prop-a1-kummer`. -/
theorem isIso_derivedBaseChangeMap_app_tateObject_multiplicativeGroup [HasInvertibleExponent Λ G]
    [HasInvertibleExponent Λ G'] :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq).app
        (tateObject Λ G 1)) := by
  let π := j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let π' := j' ≫ 𝔸(ULift.{u} (Fin 1); Y') ↘ Y'
  let q := AffineSpace.complementMap g j j' hj hj'
  let sq := (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq
  let BC := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  let K := tateObject Λ G 1
  let M := tateObject Λ Y 1
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  have hG := isZero_cohomology_multiplicativeGroup Λ j₀ hj₀
  let eG₀ := (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
  let eG₁ := (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some
  obtain ⟨LT', -, hLT', ⟨eTY'⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y' 1
  let H := fun (S : Scheme.{u}) (n : ℤ) ↦ _root_.DerivedCategory.homologyFunctor
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n
  -- `H^n` of a pullback along `g`
  have hpull : ∀ (n : ℤ) {A B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (f : A ⟶ B), IsIso ((H Y n).map f) →
        IsIso ((H Y' n).map ((L((g)^*[ModuleCat.{u + 1} Λ])).map f)) := by
    intro n A B f hf
    have : IsIso ((H Y n ⋙ (g)^*[ModuleCat.{u + 1} Λ]).map f) := by
      change IsIso (((g)^*[ModuleCat.{u + 1} Λ]).map ((H Y n).map f))
      infer_instance
    exact (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso _ g n) f).1 this
  have hzpull : ∀ (n : ℤ) (A : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))), IsZero ((H Y n).obj A) →
        IsZero ((H Y' n).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj A)) := fun n A hA ↦
    (Functor.map_isZero ((g)^*[ModuleCat.{u + 1} Λ]) hA).of_iso
      ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) g n).app A).symm
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  by_cases h0 : n = 0
  · subst h0
    have hu := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq M
    have h₁ : IsIso ((H Y 0).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app M)) :=
      isIso_homology_zero_unit_tateObject_multiplicativeGroup Λ aY j hj
    have h₂ : IsIso ((H Y' 0).map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        π').unit.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M))) :=
      isIso_homology_zero_unit_multiplicativeGroup_of_cohomology Λ aY' j₀ hj₀ hG eG₀ eG₁ j' hj'
        (constructibleFiniteTor_of_iso Λ (leftDerivedUpperStarTateObjectIso g 1).symm
          (boundedConstructibleFiniteTor_tateObject Λ Y' 1))
        (leftDerivedUpperStarTateObjectIso g 1 ≪≫ eTY') hLT'
    have h₃ : IsIso ((H Y' 0).map (BC.app ((L((π)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
      have hc := congrArg (H Y' 0).map hu
      simp only [Functor.map_comp] at hc
      have := hpull 0 _ h₁
      have : IsIso ((H Y' 0).map ((L((g)^*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app M)) ≫
          (H Y' 0).map (BC.app ((L((π)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
        rw [hc]
        infer_instance
      exact IsIso.of_isIso_comp_left ((H Y' 0).map ((L((g)^*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app M))) _
    have hnat := congrArg (H Y' 0).map
      (BC.naturality (leftDerivedUpperStarTateObjectIso (Λ := Λ) π 1).hom)
    simp only [Functor.map_comp] at hnat
    have : IsIso ((H Y' 0).map ((R((π)_*[ModuleCat.{u + 1} Λ]) ⋙
        L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso (Λ := Λ) π 1).hom) ≫
        (H Y' 0).map (BC.app K)) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left ((H Y' 0).map ((R((π)_*[ModuleCat.{u + 1} Λ]) ⋙
        L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso (Λ := Λ) π 1).hom))
      _
  by_cases h1 : n = 1
  · subst h1
    let θπ := leftDerivedUpperStarConstantComplexIso Λ π
    let θq := leftDerivedUpperStarConstantComplexIso Λ q
    let θg := leftDerivedUpperStarConstantComplexIso Λ g
    let κ := kummerClass Λ (AffineSpace.unitLineCoord j hj)
    let κ' := kummerClass Λ (AffineSpace.unitLineCoord j' hj')
    let κb := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).homEquiv _ _
      (θπ.hom ≫ κ)
    have hκb : IsIso ((H Y 0).map κb) := isIso_homology_zero_kummerClassAdjoint Λ aY j hj
    have hmate := derivedBaseChangeMap_app_homEquiv Λ sq (θπ.hom ≫ κ)
    -- `Lq^* κ(t) = κ(t')` up to isomorphisms
    let C := ((L((q)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app (tateObject Λ G 1) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso q 1)
    have hnat : (L((q)^*[ModuleCat.{u + 1} Λ])).map κ = θq.hom ≫ κ' ≫ C.inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact leftDerivedUpperStar_map_kummerClass_coord Λ (g := g) (j := j) (hj := hj) (j' := j')
        (hj' := hj')
    let A := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).app (constantComplex Λ Y) ≪≫
      (L((q)^*[ModuleCat.{u + 1} Λ])).mapIso θπ ≪≫ θq
    let Bι := (L((π')^*[ModuleCat.{u + 1} Λ])).mapIso θg.symm ≪≫ A
    have hgen := isIso_homology_zero_kummerClassAdjoint_of_cohomology Λ aY'
      (kummerClass_coord_smul_eq_zero Λ) j₀ hj₀ hG eG₀ eG₁ j' hj' Bι
    have hR : (L((g)^*[ModuleCat.{u + 1} Λ])).map κb ≫ BC.app (K⟦(1 : ℤ)⟧) =
        θg.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π').homEquiv _ _
          (Bι.hom ≫ κ') ≫ (R((π')_*[ModuleCat.{u + 1} Λ])).map C.inv := by
      rw [hmate, ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
      congr 1
      simp only [Bι, A, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
        Category.assoc, Functor.map_comp]
      rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact congrArg (fun f ↦ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (constantComplex Λ Y) ≫ (L((q)^*[ModuleCat.{u + 1} Λ])).map θπ.hom ≫ f) hnat
    have h₂ : IsIso ((H Y' 0).map (BC.app (K⟦(1 : ℤ)⟧))) := by
      have hc := congrArg (H Y' 0).map hR
      simp only [Functor.map_comp] at hc
      have := hpull 0 _ hκb
      have : IsIso ((H Y' 0).map ((L((g)^*[ModuleCat.{u + 1} Λ])).map κb) ≫
          (H Y' 0).map (BC.app (K⟦(1 : ℤ)⟧))) := by
        rw [hc]
        infer_instance
      exact IsIso.of_isIso_comp_left ((H Y' 0).map ((L((g)^*[ModuleCat.{u + 1} Λ])).map κb)) _
    have hs := NatTrans.app_shift BC (1 : ℤ) K
    rw [hs, Functor.map_comp, Functor.map_comp] at h₂
    have h₃ : IsIso ((H Y' 0).map ((BC.app K)⟦(1 : ℤ)⟧')) := by
      have := IsIso.of_isIso_comp_left ((H Y' 0).map
        (((R((π)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso
          (1 : ℤ)).hom.app K)) ((H Y' 0).map ((BC.app K)⟦(1 : ℤ)⟧') ≫ (H Y' 0).map
        (((L((q)^*[ModuleCat.{u + 1} Λ]) ⋙ R((π')_*[ModuleCat.{u + 1} Λ])).commShiftIso
          (1 : ℤ)).inv.app K))
      exact IsIso.of_isIso_comp_right _ ((H Y' 0).map
        (((L((q)^*[ModuleCat.{u + 1} Λ]) ⋙ R((π')_*[ModuleCat.{u + 1} Λ])).commShiftIso
          (1 : ℤ)).inv.app K))
    exact (NatIso.isIso_map_iff ((H Y' 0).shiftIso (1 : ℤ) 0 1 (by norm_num)) (BC.app K)).1 h₃
  · refine ⟨⟨0, (hzpull n _ ?_).eq_of_src _ _, ((?_ : IsZero _)).eq_of_src _ _⟩⟩
    · exact isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup Λ aY j hj n h0 h1
    · exact (isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup Λ aY' j' hj' n h0
        h1).of_iso ((H Y' n).mapIso ((R((π')_*[ModuleCat.{u + 1} Λ])).mapIso
          (leftDerivedUpperStarTateObjectIso q 1)))

end BaseChange

end Etale

end AlgebraicGeometry
