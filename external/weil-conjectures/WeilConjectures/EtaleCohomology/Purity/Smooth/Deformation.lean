/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpacePurity
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# DNC invariance of the section dualizing line

The deformation to the normal cone of a *section* transports the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section to the section invariant of
its normal cone with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

Given a deformation datum `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with section `s̃`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is
`F = Ls̃^* ω_{g̃}`. The blueprint argument has three steps:

* étale-locally on `B` the family is the standard family `a^* 𝒞(𝔸^d, 0)`, so `F` and `𝒞(g, s)`
  are shifts and twists of lisse rank-one sheaves (`lem-pur-concentrated-complex-shift`);
* the normalized local comparisons `F ≅ La^* 𝒞(g, s)` glue, by `𝔸¹`-invariance
  (`lemma-section-normal-bundle--1`), to a global one, for the projection `a : 𝔸¹_B ⟶ B`;
* restricting to `t = 0` gives `𝒞(g, s) ≅ 𝒞(π_N, 0_N)`, the fibres of `F` at `t = 1` and
  `t = 0` being the two section invariants by base change for the cohomologically smooth `g̃`.

## Implementation notes

The deformation space is carried as data, not constructed (see
`WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`). Its étale-local coordinates
(`prose-09-12` (2), (4), (5)) are a field of the datum; from them,
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`
computes the family object over an étale cover of `B` as the one of the standard pair
`(𝔸^d → B, 0)`, pulled back from the base. The sheaf-theoretic inputs are base change for the
smooth `g̃` and `Re^! ≅ e^*` for an étale `e` (`lem-pur-co-smooth-etale-locality`).

The family comparison `κ : F ≅ La^* 𝒞(g, s)` is pinned down by its restriction `θ` at `t = 1`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.existsUnique_familyObject_iso`), so
its compatibility with base change in `B` is a statement about this unique comparison:
restricted along any `u : B' ⟶ B` it is the unique comparison normalized against `Lu^* θ`
(`Scheme.Hom.DeformationToNormalConeData.leftDerivedUpperStar_familyObject_iso_baseChange`).

The fibre identifications `θ₁ : i₁^* F ≅ 𝒞(g, s)` and `θ₀ : i₀^* F ≅ 𝒞(π_N, 0_N)` come from
the base change isomorphism of `proposition-exceptional-inverse-image-smooth-morphism` (c), which is
only known to exist, so they are arguments of the normalization in coordinates
(`AlgebraicGeometry.Etale.existsUnique_iso_sectionInvariant_normalCone`): for coordinates `e`
over a surjective `u : B' ⟶ B`, the DNC isomorphism is the unique one which after `Lu^*` is the
identity of the standard object, read through `e` at `t = 1` and at `t = 0`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObject`: the family object
  `F = Ls̃^* ω_{g̃}`.

## Main statements

In the list below, `DeformationToNormalConeData` abbreviates
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`.

- `AlgebraicGeometry.Etale.exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso`: an
  object which is étale-locally `Λ(m)[2m]` is a lisse rank-one sheaf, twisted and shifted.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sectionInvariant`: base change
  of section invariants.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_of_etale_chart`: section invariants
  through an étale chart to `𝔸^d`.
- `DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`: étale-locally the family
  is the standard family.
- `DeformationToNormalConeData.exists_nonempty_iso_familyObject_twistShift`,
  `DeformationToNormalConeData.exists_nonempty_iso_sectionInvariant_twistShift`:
  the family object and the section invariant are lisse rank-one sheaves, twisted and shifted.
- `DeformationToNormalConeData.leftDerivedUpperStar_familyObject_iso_baseChange`: the
  comparison commutes with base change.
- `DeformationToNormalConeData.nonempty_iso_familyObject_leftDerivedUpperStar`,
  `DeformationToNormalConeData.existsUnique_familyObject_iso`:
  the family is constant along `𝔸¹_B`, by a comparison that is unique once normalized at
  `t = 1`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`: DNC invariance.
- `AlgebraicGeometry.Etale.existsUnique_iso_sectionInvariant_normalCone`: its normalization in
  coordinates and uniqueness.
- `AlgebraicGeometry.Etale.exists_iso_sectionInvariant_normalCone`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStar_mapIso_iso_sectionInvariant_normalCone`: its
  compatibility with étale localization and arbitrary base change in `B`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

omit [Finite Λ] in
/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Shifts and twists of lisse rank-one sheaves are detected on an étale cover.* Let
`u : U ⟶ T` be surjective and étale and `K ∈ D(T_ét, Λ)` with `Lu^* K ≅ Λ_U(m)[2m]`. Then
`K ≅ L(m)[2m]` for a finite locally constant sheaf `L` on `T`, free of rank one at every
geometric point.

Untwisting, `Lu^* (K(-m)[-2m]) ≅ Λ_U` is the constant sheaf in degree zero, so by the lemma
`K(-m)[-2m]` is its own `H⁰` placed in degree zero and `H⁰` is finite locally constant; its
stalks are those of `Λ_U`, a geometric point of `T` lifting to `U`. -/
theorem exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso {U T : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [Surjective u] [HasInvertibleExponent Λ T] (m : ℤ)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (twistShift Λ U m).obj (constantComplex Λ U)) :
    ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (K ≅ (twistShift Λ T m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  have : HasInvertibleExponent Λ U := .of_hom u
  let K₀ := (twistShift Λ T (-m)).obj K
  -- untwisting, `Lu^* K₀` is the unit sheaf in degree zero
  let e₀ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K₀ ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
    leftDerivedUpperStarTwistShiftIso Λ u (-m) K ≪≫ (twistShift Λ U (-m)).mapIso e ≪≫
      twistShiftTwistShiftIso Λ U m (-m) _ ≪≫ twistShiftZeroIso Λ U (by ring) _ ≪≫
      constantComplexIsoSingleFunctor Λ U
  obtain ⟨c⟩ := _root_.DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj K₀ 0
    (isZero_homology_of_leftDerivedUpperStar_iso Λ u e₀)
  refine ⟨_, isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso Λ u e₀,
    fun Ω _ _ x ↦ ?_, ⟨(twistShiftZeroIso Λ T (by ring) K).symm ≪≫
      (twistShiftTwistShiftIso Λ T (-m) m K).symm ≪≫ (twistShift Λ T m).mapIso c⟩⟩
  -- the stalk at a lift `x'` of `x` is that of `u^* H⁰(K₀) ≅ H⁰(Lu^* K₀) ≅ Λ_U`
  obtain ⟨x', rfl⟩ := exists_comp_eq_of_etale_of_surjective u x
  exact ⟨((Etale.upperStarCompSheafFiberIso _ u x').app _).symm ≪≫
    (pointSmallEtale x').sheafFiber.mapIso
      (((leftDerivedUpperStarHomologyFunctorIso _ u 0).app K₀) ≪≫
        (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e₀ ≪≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _) ≪≫
    ((pointSmallEtale x').uliftSheafFiberIso _).symm.app _ ≪≫ sheafFiberUnitIso _ x'⟩

omit [HasTateTwist Λ] in
/-- Blueprint `prose-09-12`: Geometry of the deformation

*Base change of section invariants*, the input of the two fibre identifications
`i₁^* F ≅ 𝒞(g, s)` and `i₀^* F ≅ 𝒞(π_N, 0_N)` of clause (1). In a cartesian square with
`f : X ⟶ Y` smooth and separated and sections `s` of `f` and `s'` of its base change `f'`
compatible with `g' : X' ⟶ X`, base change for the cohomologically smooth `f`
(`proposition-exceptional-inverse-image-smooth-morphism` (c)) gives `Lg^* 𝒞(f, s) ≅ 𝒞(f', s')`.
Smooth base change needs the base `Y` to be quasi-separated and `f'` to be quasi-compact. -/
theorem nonempty_iso_leftDerivedUpperStar_sectionInvariant {X Y X' Y' : Scheme.{u}} {d : ℕ}
    (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [HasCompactification f'] [QuasiSeparatedSpace Y]
    [QuasiCompact f'] (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ g' = g ≫ s) :
    Nonempty ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ f s) ≅
      sectionInvariant Λ f' s') := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
  exact ⟨((leftDerivedUpperStarComp _ g s).app _).symm ≪≫
    (leftDerivedUpperStarComp _ s' g' (g ≫ s) hs.symm).app _ ≪≫
    (L((s')^*[ModuleCat.{u + 1} Λ])).mapIso (e.app _ ≪≫
      (rightDerivedUpperShriek Λ f').mapIso
        (leftDerivedUpperStarConstantComplexIso Λ g))⟩

omit [HasTateTwist Λ] in
/-- *Section invariants through an étale chart.* Let `g' : X ⟶ T` be compactifiable, `j : W ⟶ X`
a quasi-compact open immersion and `c : W ⟶ 𝔸^d_T` a quasi-compact étale map over `T`, with
`j ≫ g' = c ≫ π`, and let `σ : T ⟶ W` be a section carried by `c` to the zero section. If
`ω_π ≅ K` for some `K ∈ D^b_{ctf}`, then `𝒞(g', σ ≫ j) ≅ 𝒞(π, 0)`:

`Lσ^* Lj^* ω_{g'} ≅ Lσ^* Rj^! Rg'^! Λ ≅ Lσ^* R(j ≫ g')^! Λ = Lσ^* R(c ≫ π)^! Λ ≅ Lσ^* Rc^! ω_π
  ≅ Lσ^* Lc^* ω_π`,

by `Rj^! ≅ j^*` for the open immersion `j`, the composition of exceptional inverse images, and
`Rc^! ≅ Lc^*` on `D^b_{ctf}` for the étale `c` (`lem-pur-co-smooth-etale-locality`). -/
theorem nonempty_iso_sectionInvariant_of_etale_chart {X W T : Scheme.{u}} {d : ℕ}
    (g' : X ⟶ T) [HasCompactification g'] (j : W ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (c : W ⟶ 𝔸(ULift.{u} (Fin d); T)) [_root_.AlgebraicGeometry.Etale c] [QuasiCompact c]
    [HasCompactification c] [HasInvertibleExponent Λ W]
    (hjc : j ≫ g' = c ≫ 𝔸(ULift.{u} (Fin d); T) ↘ T) (σ : T ⟶ W)
    (hσc : σ ≫ c = AffineSpace.zeroSection (ULift.{u} (Fin d)) T)
    {K : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin d); T).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ _ K)
    (ω : dualizingComplex Λ (𝔸(ULift.{u} (Fin d); T) ↘ T) ≅ K) :
    Nonempty (sectionInvariant Λ g' (σ ≫ j) ≅
      sectionInvariant Λ (𝔸(ULift.{u} (Fin d); T) ↘ T)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) T)) := by
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  have : HasCompactification (j ≫ g') := .comp_of_isOpenImmersion g' j
  have : HasCompactification (c ≫ 𝔸(ULift.{u} (Fin d); T) ↘ T) := .of_eq hjc
  have : QuasiCompact (j ≫ g') := hjc ▸ inferInstance
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j g'
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ hjc
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ c (𝔸(ULift.{u} (Fin d); T) ↘ T)
  obtain ⟨e₄⟩ := nonempty_iso_rightDerivedUpperShriek_obj_of_etale Λ c K hK
  exact ⟨(leftDerivedUpperStarComp _ σ j).app _ ≪≫
    (L((σ)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
        ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫
        (e₁.app _).symm ≪≫ e₂.app _ ≪≫ e₃.app _ ≪≫
        (rightDerivedUpperShriek Λ c).mapIso ω ≪≫ e₄ ≪≫
        (L((c)^*[ModuleCat.{u + 1} Λ])).mapIso ω.symm) ≪≫
    ((leftDerivedUpperStarComp _ σ c _ hσc.symm).app _).symm⟩

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section

The *family object* `F = Ls̃^* ω_{g̃}` on `𝔸¹_B` of a deformation datum: the section invariant
of the deformation `g̃ : 𝒟_s V ⟶ 𝔸¹_B` and its section `s̃`. -/
noncomputable abbrev familyObject :
    _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  sectionInvariant Λ D.proj D.sect

variable [HasInvertibleExponent Λ B]

omit [Finite Λ] [HasTateTwist Λ] in
include D in
/-- The exponent of `Λ` is invertible on the deformation space as soon as it is on `B`. -/
theorem hasInvertibleExponent_scheme : HasInvertibleExponent Λ D.scheme :=
  HasInvertibleExponent.of_hom (D.proj ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)

omit [HasTateTwist Λ] in
/-- The family object is ⊗-invertible: `ω_{g̃}` is by cohomological smoothness of the smooth
separated `g̃` (`proposition-exceptional-inverse-image-smooth-morphism` (a)), and derived pullback
along `s̃` preserves invertibility. -/
theorem isInvertible_familyObject :
    Etale.DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (D.familyObject Λ) :=
  have := D.hasInvertibleExponent_scheme Λ
  Etale.DerivedCategory.isInvertible.leftDerivedUpperStar D.sect
    (isInvertible_dualizingComplex Λ (d := d) D.proj)

variable [HasCompactification g]

omit [HasTateTwist Λ] in
/-- The fibre of the family at `t = 1` is the section invariant of `(g, s)`
(`prose-09-12` (1)): `Li₁^* F ≅ 𝒞(g, s)`, by base change for `g̃` along the
unit section. -/
theorem nonempty_iso_leftDerivedUpperStar_oneSection_familyObject [QuasiSeparatedSpace B]
    [QuasiCompact g] :
    Nonempty ((L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :=
  have := D.hasInvertibleExponent_scheme Λ
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj D.isPullback_oneFibre
    D.sect s D.comp_oneFibre

variable {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]

omit [HasCompactification g] in
include aB in
/-- Blueprint `prose-09-12`: Geometry of the deformation

*Clauses (2), (4) and (5): the family is étale-locally the standard family.* There is a
surjective étale `u : B' ⟶ B`, with `B'` separated of finite type over `k`, over which

`F|_{𝔸¹_{B'}} ≅ a'^* 𝒞(𝔸^d_{B'} → B', 0)`.

Take the étale coordinates of the datum (`exists_etale_coordinates`): over `u`, an open
`j : W ⟶ 𝒟'` of the base-changed deformation `g' : 𝒟' ⟶ 𝔸¹_{B'}` containing its section `σ`,
and an étale `c : W ⟶ 𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}` carrying `σ` to the zero section. Then

`F|_{𝔸¹_{B'}} ≅ Lσ^* Lj^* ω_{g'} ≅ Lσ^* Rj^! ω_{g'} ≅ Lσ^* Rc^! ω_π ≅ Lσ^* Lc^* ω_π ≅ L0^* ω_π`,

by base change for `g̃` (`proposition-exceptional-inverse-image-smooth-morphism` (c)), `Rj^! ≅ j^*`
for the open immersion `j`, the composition of exceptional inverse images along `j ≫ g' = c ≫ π`,
and `Rc^! ≅ c^*` for the étale `c` (`lem-pur-co-smooth-etale-locality`). Both `L0^* ω_π` and
`a'^* 𝒞(𝔸^d_{B'} → B', 0)` are `Λ(d)[2d]` by affine-space purity
(`proposition-purity-vector-bundles`). -/
theorem exists_etale_nonempty_iso_familyObject [HasTateTwist.IsNormalized Λ]
    [QuasiCompact D.proj] :
    ∃ (B' : Scheme.{u}) (u : B' ⟶ B), _root_.AlgebraicGeometry.Etale u ∧ Surjective u ∧
      IsSeparated (u ≫ aB) ∧
      Nonempty ((L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
          (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B'))) := by
  obtain ⟨B', v, W, j, c, σ, hv, hsurj, hsep, hj, hjqc, hc, hcqc, hcc, hjc, hσj, hσc⟩ :=
    D.exists_etale_coordinates
  let T := 𝔸(ULift.{u} (Fin 1); B')
  let v₁ := AffineSpace.map (ULift.{u} (Fin 1)) v
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have := D.hasInvertibleExponent_scheme Λ
  have : HasInvertibleExponent Λ B' := .of_hom v
  have : HasInvertibleExponent Λ T := .of_hom (T ↘ B')
  have : HasInvertibleExponent Λ (pullback D.proj v₁) := .of_hom (pullback.fst D.proj v₁)
  have : HasInvertibleExponent Λ W := .of_hom j
  -- `Lv₁^* F ≅ 𝒞(g', σ ≫ j)`, by base change for `g̃` along `v₁`
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj
    (IsPullback.of_hasPullback D.proj v₁) D.sect (σ ≫ j) ((Category.assoc _ _ _).trans hσj)
  -- `𝒞(g', σ ≫ j) ≅ 𝒞(𝔸^d_T → T, 0)` through the chart, with `ω_π ≅ Λ(d)[2d]`
  -- (`proposition-purity-vector-bundles`)
  obtain ⟨ω⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d T (T ↘ B' ≫ v ≫ aB)
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_of_etale_chart Λ (pullback.snd D.proj v₁) j c hjc
    σ hσc ((boundedConstructibleFiniteTor_tateObject Λ _ d).shift (2 * d))
    (ω ≪≫ twistShiftConstantComplexIso Λ _ d)
  -- both standard section invariants are `Λ(d)[2d]`
  obtain ⟨c₁⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d T (T ↘ B' ≫ v ≫ aB)
  obtain ⟨c₀⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d B' (v ≫ aB)
  refine ⟨B', v, hv, hsurj, inferInstanceAs (IsSeparated (v ≫ aB)), ⟨?_⟩⟩
  exact e₁ ≪≫ e₂ ≪≫ c₁ ≪≫
    ((twistShift Λ T d).mapIso (leftDerivedUpperStarConstantComplexIso Λ (T ↘ B'))).symm ≪≫
    (leftDerivedUpperStarTwistShiftIso Λ _ d _).symm ≪≫
    (L((T ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso c₀.symm

variable [HasTateTwist.IsNormalized Λ]

include aB in
/-- The étale-local data of the family used by `lemma-section-normal-bundle--1`: over the cover
`u : B' ⟶ B` of `prose-09-12` (2), with `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B` its base
change, the family is `Lv₁^* F ≅ La'^* 𝒞₀` for the standard section invariant
`𝒞₀ = 𝒞(𝔸^d_{B'} → B', 0) ≅ Λ_{B'}(d)[2d]` (`proposition-purity-vector-bundles`), and restricting at
`t = 1` gives `φ : Lu^* 𝒞(g, s) ≅ 𝒞₀`, related to the base change `θ : Li₁^* F ≅ 𝒞(g, s)` by
`Li₁'^* e = (Li₁'^* Lv₁^* F ≅ Lu^* Li₁^* F) ≫ Lu^* θ ≫ φ` up to `Li₁'^* La'^* ≅ 𝟭`. -/
theorem exists_etale_familyObject_data [QuasiCompact D.proj]
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    ∃ (B' : Scheme.{u}) (u : B' ⟶ B), _root_.AlgebraicGeometry.Etale u ∧ Surjective u ∧
      IsSeparated (u ≫ aB) ∧
      Nonempty (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) B') ≅
          (twistShift Λ B' d).obj (constantComplex Λ B')) ∧
      ∃ (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
          (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B')))
        (φ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s) ≅
          sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B')),
        (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])).map e.hom ≫
            (leftDerivedUpperStarCompSectionIso _ _ _
              (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')).hom.app _ =
          (((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
              (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.app _ ≫
            (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
              (AffineSpace.oneSection_comp_map u)).hom.app _) ≫
            (L((u)^*[ModuleCat.{u + 1} Λ])).map θ.hom) ≫ φ.hom := by
  obtain ⟨B', u, hu, hsurj, hsep, ⟨e⟩⟩ := D.exists_etale_nonempty_iso_familyObject Λ aB
  have : HasInvertibleExponent Λ B' := .of_hom u
  obtain ⟨c⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d B' (u ≫ aB)
  let i₁' := AffineSpace.oneSection (ULift.{u} (Fin 1)) B'
  let ε' := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i₁' _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  let dF := ((leftDerivedUpperStarComp _ i₁' (AffineSpace.map (ULift.{u} (Fin 1)) u)).app
      (D.familyObject Λ)).symm ≪≫
    (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
      (AffineSpace.oneSection_comp_map u)).app (D.familyObject Λ)
  refine ⟨B', u, hu, hsurj, hsep, ⟨c⟩, e,
    (dF ≪≫ (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso θ).symm ≪≫
      (L((i₁')^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ ε'.app _, ?_⟩
  exact (Iso.hom_inv_id_assoc (dF ≪≫ (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso θ) _).symm

include D aB in
/-- Blueprint `lemma-section-normal-bundle--1`: The deformation family is constant along the
affine line

*Clause (1) for the section invariant.* There is a finite locally constant sheaf `L₁` on `B`,
free of rank one at every geometric point, with `𝒞(g, s) ≅ L₁(d)[2d]`: over the étale cover of
`prose-09-12` (2) it is the standard section invariant `Λ(d)[2d]`
(`proposition-purity-vector-bundles`), and `lem-pur-concentrated-complex-shift` applies. -/
theorem exists_nonempty_iso_sectionInvariant_twistShift [QuasiCompact D.proj] :
    ∃ L : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ B),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (sectionInvariant Λ g s ≅
        (twistShift Λ B d).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, -, ⟨c⟩, -, φ, -⟩ := D.exists_etale_familyObject_data Λ aB θ
  exact exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso Λ u d _ (φ ≪≫ c)

include aB in
/-- Blueprint `lemma-section-normal-bundle--1`: The deformation family is constant along the
affine line

*Clause (1), the family is a shift of a lisse line.* There is a finite locally constant sheaf
`L_F` on `𝔸¹_B`, free of rank one at every geometric point, with `F ≅ L_F(d)[2d]`: over the
étale cover of `prose-09-12` (2) the family is the pullback of the standard
section invariant `Λ(d)[2d]` (`proposition-purity-vector-bundles`), and
`lem-pur-concentrated-complex-shift` applies. The same statement for `𝒞(g, s)` is
`exists_nonempty_iso_sectionInvariant_twistShift`. -/
theorem exists_nonempty_iso_familyObject_twistShift [QuasiCompact D.proj] :
    ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); B)),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (D.familyObject Λ ≅ (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) d).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, -, ⟨c⟩, e, -⟩ := D.exists_etale_familyObject_data Λ aB θ
  have : HasInvertibleExponent Λ B' := .of_hom u
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B') :=
    .of_hom (𝔸(ULift.{u} (Fin 1); B') ↘ B')
  have : _root_.AlgebraicGeometry.Etale (AffineSpace.map (ULift.{u} (Fin 1)) u) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (AffineSpace.isPullback_map u).flip hu
  have : Surjective (AffineSpace.map (ULift.{u} (Fin 1)) u) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (AffineSpace.isPullback_map u).flip hsurj
  exact exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso Λ
    (AffineSpace.map (ULift.{u} (Fin 1)) u) d _
    (e ≪≫ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫
      leftDerivedUpperStarTwistShiftIso Λ _ d _ ≪≫
      (twistShift Λ _ d).mapIso (leftDerivedUpperStarConstantComplexIso Λ _))

include aB in
/-- Blueprint `lemma-section-normal-bundle--1`: The deformation family is constant along the
affine line

*Clause (2), constancy along the affine line.* For the projection `a : 𝔸¹_B ⟶ B` there is an
isomorphism

`κ : F ≅ La^* 𝒞(g, s)`,

so that the family object is the pullback of its own fibre `𝒞(g, s)` at `t = 1`.

Over the étale cover `u : B' ⟶ B` of `prose-09-12` (2) the family is
`La'^* 𝒞₀` for the standard section invariant `𝒞₀ ≅ Λ(d)[2d]`, which gives the local shape
and, through the fibre `φ : Lu^* 𝒞(g, s) ≅ 𝒞₀` at `t = 1`, a comparison
`κ' : Lv₁^* F ≅ La'^* Lu^* 𝒞(g, s)` normalized at `t = 1`. These glue by `𝔸¹`-invariance
(`lemma-section-normal-bundle--1`). -/
theorem nonempty_iso_familyObject_leftDerivedUpperStar [QuasiCompact D.proj] :
    Nonempty (D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s)) := by
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, hsep, ⟨c⟩, e, φ, h⟩ := D.exists_etale_familyObject_data Λ aB θ
  have : HasInvertibleExponent Λ B' := .of_hom u
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B') :=
    .of_hom (𝔸(ULift.{u} (Fin 1); B') ↘ B')
  let a' := 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  let ε' := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ a'
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  -- the local shape: `Lv₁^* F ≅ La'^* Λ(d)[2d] ≅ Λ(d)[2d]`
  have hF : ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); B').smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); B')),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      ∃ m n : ℤ, Nonempty
        ((L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
            (D.familyObject Λ) ≅
          ((tateTwist Λ _ m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦n⟧) :=
    ⟨𝟙_ _, inferInstance, fun Ω _ _ x ↦
      ⟨((pointSmallEtale x).uliftSheafFiberIso _).symm.app _ ≪≫ sheafFiberUnitIso _ x⟩, d,
      2 * d, ⟨e ≪≫ (L((a')^*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫
        leftDerivedUpperStarTwistShiftIso Λ _ d _ ≪≫
        (twistShift Λ _ d).mapIso (leftDerivedUpperStarConstantComplexIso Λ _ ≪≫
          constantComplexIsoSingleFunctor Λ _)⟩⟩
  -- the normalized local comparison `κ' = e ≫ La'^* φ⁻¹`
  have := hu; have := hsurj; have := hsep
  obtain ⟨κ, -, -⟩ := existsUnique_iso_leftDerivedUpperStar_of_etale Λ aB (D.familyObject Λ)
    (sectionInvariant Λ g s) θ u hF (e ≪≫ (L((a')^*[ModuleCat.{u + 1} Λ])).mapIso φ.symm) (by
      have hn := ε'.hom.naturality φ.inv
      dsimp at hn
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Category.assoc]
      rw [hn, reassoc_of% h]
      simp)
  exact ⟨κ⟩

include aB in
/-- Blueprint `lemma-section-normal-bundle--1`: The deformation family is constant along the
affine line

*Clause (3), normalization and uniqueness.* For every identification
`θ : i₁^* F ≅ 𝒞(g, s)` of the fibre of the family at `t = 1` (for instance the base change
identification of `prose-09-12` (1), see
`nonempty_iso_leftDerivedUpperStar_oneSection_familyObject`)
there is a unique isomorphism `κ : F ≅ La^* 𝒞(g, s)` restricting to `θ` at `t = 1`, under
`i₁^* a^* ≅ 𝟭`.

Existence: twist any comparison of clause (2) by the automorphism of `𝒞(g, s)` measuring its
failure to restrict to `θ`. Uniqueness: `F` is invertible, and a comparison between an
invertible complex on `𝔸¹_B` and a pullback from `B` is determined at `t = 1`
(`lemma-section-normal-bundle--1`). -/
theorem existsUnique_familyObject_iso [QuasiCompact D.proj]
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    ∃! κ : D.familyObject Λ ≅
        (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s),
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
        (leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.app _ = θ.hom := by
  obtain ⟨κ₀⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ aB
  let ε := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  let i₁ := L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])
  let a := L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])
  -- twisting a comparison by an automorphism `ψ` of `𝒞(g, s)` twists its restriction by `ψ`
  have key (κ : D.familyObject Λ ≅ a.obj (sectionInvariant Λ g s))
      (ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ g s) :
      i₁.map (κ ≪≫ a.mapIso ψ).hom ≫ ε.hom.app _ = (i₁.map κ.hom ≫ ε.hom.app _) ≫ ψ.hom := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    congr 1
    exact ε.hom.naturality ψ.hom
  let ψ := (i₁.mapIso κ₀ ≪≫ ε.app _).symm ≪≫ θ
  have hψ : (i₁.map κ₀.hom ≫ ε.hom.app _) ≫ ψ.hom = θ.hom := by simp [ψ]
  refine ⟨κ₀ ≪≫ a.mapIso ψ, (key κ₀ ψ).trans hψ, fun κ hκ ↦ ?_⟩
  refine eq_of_leftDerivedUpperStar_oneSection_eq Λ _ _ (D.isInvertible_familyObject Λ) _ _ ?_
  rw [← cancel_mono (ε.hom.app _)]
  exact hκ.trans ((key κ₀ ψ).trans hψ).symm

omit [HasTateTwist.IsNormalized Λ] in
/-- Blueprint `lemma-section-normal-bundle--1`: The deformation family is constant along the
affine line

*Clause (4), base change.* The normalized comparison commutes with arbitrary base change
`u : B' ⟶ B`, in particular with étale localization on `B`. Let `κ : F ≅ La^* 𝒞(g, s)` restrict
to `θ` at `t = 1` (clause (3)), and let `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B` be the base change of `u`. Then
the restriction `κ|_{B'} : Lv₁^* F ≅ Lv₁^* La^* 𝒞(g, s) ≅ La'^* Lu^* 𝒞(g, s)` restricts at
`t = 1` to the restriction `Lu^* θ` of `θ`, and it is the only comparison
`Lv₁^* F ≅ La'^* Lu^* 𝒞(g, s)` doing so. -/
theorem leftDerivedUpperStar_familyObject_iso_baseChange
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (κ : D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s))
    (hκ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
        (leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.app _ = θ.hom)
    {B' : Scheme.{u}} (u : B' ⟶ B)
    (κ' : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
        (D.familyObject Λ) ≅
      (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((u)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s))) :
    (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])).map κ'.hom ≫
        (leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')).hom.app _ =
      ((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
          (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.app _ ≫
        (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
          (AffineSpace.oneSection_comp_map u)).hom.app _) ≫
        (L((u)^*[ModuleCat.{u + 1} Λ])).map θ.hom ↔
    κ'.hom = (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
      (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).inv.app _ ≫
        (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u _
          (AffineSpace.map_over (n := ULift.{u} (Fin 1)) u)).hom.app _ := by
  let i₁' := L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])
  let ε' := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  -- the restriction of `κ` is normalized against `Lu^* θ`
  have hres : i₁'.map ((L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).map
        κ.hom ≫ (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).inv.app _ ≫
        (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u _
          (AffineSpace.map_over (n := ULift.{u} (Fin 1)) u)).hom.app _) ≫ ε'.hom.app _ =
      ((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
          (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.app _ ≫
        (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
          (AffineSpace.oneSection_comp_map u)).hom.app _) ≫
        (L((u)^*[ModuleCat.{u + 1} Λ])).map θ.hom := by
    rw [Functor.map_comp, Category.assoc,
      leftDerivedUpperStar_map_comp_compSectionIso _ u _ _ _ _ _ (AffineSpace.map_over u)
        (AffineSpace.oneSection_comp_map u) (AffineSpace.oneSection_comp_over _ B)
        (AffineSpace.oneSection_comp_over _ B')]
    have n₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
      (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.naturality κ.hom
    have n₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
      (AffineSpace.oneSection_comp_map u)).hom.naturality κ.hom
    simp only [Functor.comp_map] at n₁ n₂
    simp only [Category.assoc]
    erw [reassoc_of% n₁, reassoc_of% n₂]
    rw [← Functor.map_comp, hκ]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hres⟩
  let κr := (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).mapIso κ ≪≫
    ((leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
      (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _).symm ≪≫
    (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u _
      (AffineSpace.map_over (n := ULift.{u} (Fin 1)) u)).app _
  have : HasInvertibleExponent Λ B' := .of_hom u
  have := eq_of_leftDerivedUpperStar_oneSection_eq Λ _ _
    (DerivedCategory.isInvertible.leftDerivedUpperStar _ (D.isInvertible_familyObject Λ))
    κ' κr (by rw [← cancel_mono (ε'.hom.app _)]; exact h.trans hres.symm)
  exact congrArg Iso.hom this
end Scheme.Hom.DeformationToNormalConeData

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}}

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, over a base
`B` separated of finite type over a field, let `N_s ⟶ B` be its normal cone with zero section
`0_N`, and let `g̃ : 𝒟_s V ⟶ 𝔸¹_B` be a deformation to the normal cone (the situation of
`prose-09-12`). There is an isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants. It is `i₀^*` of the comparison `κ : F ≅ La^* 𝒞(g, s)` of
`lemma-section-normal-bundle--1` (2), the fibre `i₀^* F` being `𝒞(π_N, 0_N)` by base change
(`prose-09-12` (1)). This is also blueprint `lemma-section-normal-bundle--1`. -/
-- The normalization in coordinates and the uniqueness are
-- `AlgebraicGeometry.Etale.existsUnique_iso_sectionInvariant_normalCone`.
theorem nonempty_iso_sectionInvariant_normalCone [HasTateTwist.IsNormalized Λ] (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] [QuasiCompact D.proj] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) := by
  have := D.hasInvertibleExponent_scheme Λ
  obtain ⟨κ⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ aB
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : QuasiCompact N.proj := MorphismProperty.of_isPullback D.isPullback_zeroFibre inferInstance
  obtain ⟨e₀⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj
    D.isPullback_zeroFibre D.sect N.zeroSection D.comp_zeroFibre
  exact ⟨((leftDerivedUpperStarCompSectionIso _ _ _
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app _).symm ≪≫
    (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso κ.symm ≪≫
    e₀⟩

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line

*Existence, compatibly with every base change.* Fix identifications `θ₁ : i₁^* F ≅ 𝒞(g, s)` and
`θ₀ : i₀^* F ≅ 𝒞(π_N, 0_N)` of the two fibres of the family object
(`prose-09-12` (1)). There is an isomorphism `Ψ : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` such
that for every base change `u : B' ⟶ B` and every `e : Lv₁^* F ≅ La'^* C₀` carrying the
restricted family to one pulled back from `C₀` on `B'`, reading `e` at `t = 1` and at `t = 0` as
`φ₁ : Lu^* 𝒞(g, s) ≅ C₀` and `φ₀ : Lu^* 𝒞(π_N, 0_N) ≅ C₀`, one has `Lu^* Ψ = φ₁ ≫ φ₀⁻¹`.

`Ψ` is `i₀^*` of the comparison `κ` normalized against `θ₁`, whose restriction to `B'` is read
off from `e` by the uniqueness of `lemma-section-normal-bundle--1` (3), (4). -/
theorem exists_iso_sectionInvariant_normalCone [HasTateTwist.IsNormalized Λ] (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] [QuasiCompact D.proj]
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection) :
    ∃ Ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection,
      ∀ {B' : Scheme.{u}} (u : B' ⟶ B)
        {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
          (D.familyObject Λ) ≅
            (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj C₀),
        (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso Ψ =
          sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
              (AffineSpace.oneSection_comp_over _ B') θ₁ e ≪≫
            (sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
              (AffineSpace.zeroSection_comp_over _ B') θ₀ e).symm := by
  have := D.hasInvertibleExponent_scheme Λ
  -- the comparison `κ` normalized against `θ₁`
  obtain ⟨κ, hκ, -⟩ := D.existsUnique_familyObject_iso Λ aB θ₁
  have hθ₁ : θ₁ = (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      κ ≪≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).app _ := Iso.ext hκ.symm
  -- `Ψ` is the fibre of `κ` at `t = 0`
  let θ₀' := (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      κ ≪≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app (sectionInvariant Λ g s)
  refine ⟨θ₀'.symm ≪≫ θ₀, fun {B'} u C₀ e ↦ ?_⟩
  have : HasInvertibleExponent Λ B' := .of_hom u
  have hv : AffineSpace.map (ULift.{u} (Fin 1)) u ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B =
      𝔸(ULift.{u} (Fin 1); B') ↘ B' ≫ u := AffineSpace.map_over u
  let κr := (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).mapIso κ ≪≫
    ((leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
      (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _).symm ≪≫
    (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u _ hv).app _
  let φ₁ := sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
    (AffineSpace.oneSection_comp_over _ B') θ₁ e
  -- the restriction of `κ` is `e` read in the coordinates `φ₁`
  have hκr : κr = e ≪≫
      (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁.symm := by
    refine eq_of_leftDerivedUpperStar_oneSection_eq Λ _ _
      (DerivedCategory.isInvertible.leftDerivedUpperStar _ (D.isInvertible_familyObject Λ))
      _ _ (leftDerivedUpperStar_map_eq_of_sectionRestrictionIso_eq _ u _
        (AffineSpace.oneSection_comp_map u) (AffineSpace.oneSection_comp_over _ B') θ₁ _ _ ?_)
    rw [sectionRestrictionIso_trans_right, hθ₁, sectionRestrictionIso_restrict _ u _ _ _ hv
      (AffineSpace.oneSection_comp_over _ B), ← hθ₁]
    exact (Iso.self_symm_id φ₁).symm
  have he : e = κr ≪≫
      (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁ := by
    rw [hκr]
    ext
    simp
  have key : sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
        (AffineSpace.zeroSection_comp_over _ B') θ₀ e =
      (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso (θ₀'.symm ≪≫ θ₀).symm ≪≫ φ₁ := by
    have h₀ : θ₀ = θ₀' ≪≫ (θ₀'.symm ≪≫ θ₀) := by simp
    calc _ = sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
          (AffineSpace.zeroSection_comp_over _ B') (θ₀' ≪≫ (θ₀'.symm ≪≫ θ₀))
            (κr ≪≫ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁) := by
          rw [← he, ← h₀]
      _ = _ := by
        rw [sectionRestrictionIso_trans_left, sectionRestrictionIso_trans_right,
          sectionRestrictionIso_restrict _ u _ _ _ hv (AffineSpace.zeroSection_comp_over _ B)]
        simp
  rw [key]
  ext
  simp

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line

*Normalization in coordinates and uniqueness.* Fix identifications `θ₁ : i₁^* F ≅ 𝒞(g, s)` and
`θ₀ : i₀^* F ≅ 𝒞(π_N, 0_N)` of the two fibres of the family object
(`prose-09-12` (1)). Let `u : B' ⟶ B` be surjective and
`e : Lv₁^* F ≅ La'^* C₀` coordinates over `B'` carrying the family to a standard one, pulled back
from `C₀` on `B'` (for instance those of `prose-09-12` (2), (4), with
`C₀ = 𝒞(𝔸^d_{B'}, 0)`). Reading `e` at `t = 1` and at `t = 0` gives `φ₁ : Lu^* 𝒞(g, s) ≅ C₀` and
`φ₀ : Lu^* 𝒞(π_N, 0_N) ≅ C₀`. Then there is a unique isomorphism `Ψ : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)`
which in these coordinates is the identity of `C₀`, `Lu^* Ψ = φ₁ ≫ φ₀⁻¹`.

Existence is `exists_iso_sectionInvariant_normalCone`. Uniqueness: `𝒞(g, s)` is invertible and
`Lu^*` is faithful on its automorphisms. -/
theorem existsUnique_iso_sectionInvariant_normalCone [HasTateTwist.IsNormalized Λ] (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] [QuasiCompact D.proj]
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection)
    {B' : Scheme.{u}} (u : B' ⟶ B) [Surjective u]
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
        (D.familyObject Λ) ≅ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj C₀) :
    ∃! Ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection,
      (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso Ψ =
        sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
            (AffineSpace.oneSection_comp_over _ B') θ₁ e ≪≫
          (sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
            (AffineSpace.zeroSection_comp_over _ B') θ₀ e).symm := by
  have := D.hasInvertibleExponent_scheme Λ
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_iso_sectionInvariant_normalCone Λ d g s N D aB θ₁ θ₀
  have hinv : DerivedCategory.isInvertible Λ B (sectionInvariant Λ g s) :=
    DerivedCategory.isInvertible.of_iso θ₁
      (DerivedCategory.isInvertible.leftDerivedUpperStar _ (D.isInvertible_familyObject Λ))
  refine ⟨Ψ₀, hΨ₀ u e, fun Ψ hΨ ↦ ?_⟩
  -- two such isomorphisms differ by an automorphism of `𝒞(g, s)` trivial after `Lu^*`
  have h₁ : (L((u)^*[ModuleCat.{u + 1} Λ])).map Ψ.hom =
      (L((u)^*[ModuleCat.{u + 1} Λ])).map Ψ₀.hom :=
    congrArg Iso.hom (hΨ.trans (hΨ₀ u e).symm)
  have := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective u hinv
    (Ψ.hom ≫ Ψ₀.inv) (by
      rw [Functor.map_comp, h₁, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id])
  exact Iso.ext ((Iso.comp_inv_eq_id _).mp this)

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line

*Compatibility with étale localization and arbitrary base change in `B`.* Let
`Ψ : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` be the DNC isomorphism, normalized as in
`existsUnique_iso_sectionInvariant_normalCone` by coordinates `e` over a surjective `u : B' ⟶ B`.
Then for every base change `u' : B'' ⟶ B` (for instance an étale localization) and every
identification `e' : Lv₁'^* F ≅ La''^* C₀'` of the restricted family with one pulled back from
`B''`, `Lu'^* Ψ` is the isomorphism `φ₁' ≫ φ₀'⁻¹` read off from `e'` at `t = 1` and `t = 0`.

For `e'` the comparison `κ'` of the restricted family normalized against `Lu'^* θ₁`
(`lemma-section-normal-bundle--1` (4)), this says that `Lu'^* Ψ` is the DNC isomorphism of the
family restricted to `B''`. -/
theorem leftDerivedUpperStar_mapIso_iso_sectionInvariant_normalCone
    [HasTateTwist.IsNormalized Λ] (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] [QuasiCompact D.proj]
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection)
    {B' : Scheme.{u}} (u : B' ⟶ B) [Surjective u]
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
        (D.familyObject Λ) ≅ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj C₀)
    (Ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection)
    (hΨ : (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso Ψ =
      sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
          (AffineSpace.oneSection_comp_over _ B') θ₁ e ≪≫
        (sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
          (AffineSpace.zeroSection_comp_over _ B') θ₀ e).symm)
    {B'' : Scheme.{u}} (u' : B'' ⟶ B)
    {C₀' : _root_.DerivedCategory (Sheaf B''.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e' : (L((AffineSpace.map (ULift.{u} (Fin 1)) u')^*[ModuleCat.{u + 1} Λ])).obj
        (D.familyObject Λ) ≅
          (L((𝔸(ULift.{u} (Fin 1); B'') ↘ B'')^*[ModuleCat.{u + 1} Λ])).obj C₀') :
    (L((u')^*[ModuleCat.{u + 1} Λ])).mapIso Ψ =
      sectionRestrictionIso _ u' _ (AffineSpace.oneSection_comp_map u')
          (AffineSpace.oneSection_comp_over _ B'') θ₁ e' ≪≫
        (sectionRestrictionIso _ u' _ (AffineSpace.zeroSection_comp_map u')
          (AffineSpace.zeroSection_comp_over _ B'') θ₀ e').symm := by
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_iso_sectionInvariant_normalCone Λ d g s N D aB θ₁ θ₀
  obtain rfl := (existsUnique_iso_sectionInvariant_normalCone Λ d g s N D aB θ₁ θ₀ u e).unique hΨ
    (hΨ₀ u e)
  exact hΨ₀ u' e'

end Etale

end AlgebraicGeometry
