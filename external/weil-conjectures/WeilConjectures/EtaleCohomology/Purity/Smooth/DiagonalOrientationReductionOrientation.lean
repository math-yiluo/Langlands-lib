/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports

/-!
# The canonical orientation under the reduction of coefficients

Let `Ψ` be the derived extension of scalars along a surjection `ρ : Λ →+* Λ'` of finite
coefficient rings with principal kernel, as a change of coefficients with supports
(`AlgebraicGeometry.Etale.reductionSupportedCoefficientChange`). For `f : X ⟶ Y` smooth of
relative dimension `d` with first projection `p₁ : X ×_Y X ⟶ X`, an identification
`vω : Ψ ω_f ≅ ω'_f` of the dualizing complexes induces, through the smooth base change
`ω_{p₁} ≅ Lp₂^* ω_f` (`AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso`) and the
commutation of `Ψ` with `Lp₂^*`, an identification `Ψ ω_{p₁} ≅ ω'_{p₁}`
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexPullbackFstIso`). For this choice,
the compatibility `hC` of the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f` in
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso` holds
(`AlgebraicGeometry.Etale.map_sectionInvariantDiagonalIso_hom_comp`), by the compatibility of the
commutation of `Ψ` with the derived pullbacks with `LΔ^* Lp₂^* ≅ 𝟭`. Hence the canonical
orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with `Ψ` as soon as the frame classes of the
diagonal (`hframe`), the composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` (`hε`) and the section
invariant construction (`hL`) are
(`AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction`, blueprint
`proposition-compatibility-purity-change-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] {ρ : Λ →+* Λ'}
  {a : Λ} (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
  [HasCompactification f] [QuasiSeparatedSpace Y] [QuasiCompact f]

/-- The identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced by `vω : Ψ ω_f ≅ ω'_f` through the smooth base
change `ω_{p₁} ≅ Lp₂^* ω_f` and the commutation of `Ψ` with `Lp₂^*`. -/
noncomputable def derivedExtendScalarsDualizingComplexPullbackFstIso
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f) :
    (derivedExtendScalars hρ ha (pullback f f)).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ' (pullback.fst f f) :=
  (derivedExtendScalars hρ ha (pullback f f)).mapIso (dualizingComplexPullbackFstIso Λ f d) ≪≫
    (derivedExtendScalarsPullbackIso hρ ha (pullback.snd f f)).app _ ≪≫
      (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ'])).mapIso vω ≪≫
        (dualizingComplexPullbackFstIso Λ' f d).symm

/-- For the identification `Ψ ω_{p₁} ≅ ω'_{p₁}` induced by `vω`
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexPullbackFstIso`), the smooth base
change identifications `𝒞(p₁, Δ) ≅ ω_f` over `Λ` and `Λ'`
(`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso`) correspond. -/
theorem map_sectionInvariantDiagonalIso_hom_comp
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f) :
    (derivedExtendScalars hρ ha X).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      ((derivedExtendScalarsPullbackIso hρ ha (pullback.diagonal f)).hom.app _ ≫
          (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map
            (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω).hom) ≫
        (sectionInvariantDiagonalIso Λ' f d).hom := by
  have hs := derivedExtendScalarsPullbackMap_compSection hρ ha (pullback.diagonal f)
    (pullback.snd f f) (pullback.diagonal_snd f) (dualizingComplex Λ f)
  have hn₁ := (derivedExtendScalarsPullbackMap hρ ha (pullback.diagonal f)).naturality
    (dualizingComplexPullbackFstIso Λ f d).hom
  have hn₂ := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ') (pullback.diagonal f)
    (pullback.snd f f) (pullback.diagonal_snd f)).hom.naturality vω.hom
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn₁ hn₂
  simp only [sectionInvariantDiagonalIso, derivedExtendScalarsDualizingComplexPullbackFstIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    derivedExtendScalarsPullbackIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ']))
      (dualizingComplexPullbackFstIso Λ' f d).inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, hn₂, ← reassoc_of% hn₁, reassoc_of% hs]

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha)

/-- Blueprint `proposition-relative-dualizing-complex--1`,
`proposition-compatibility-purity-change-coefficients`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with the reduction of
coefficients.** Let `f : X ⟶ Y` be smooth separated of relative dimension `d`, `Y` separated and
locally of finite type over a field, and `vω : Ψ ω_f ≅ ω'_f`. Read `Ψ ω_{p₁} ≅ ω'_{p₁}` through
the smooth base change
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexPullbackFstIso`).
If the derived extension of scalars carries the frame classes of the diagonal over `Λ` to those
over `Λ'` (`hframe`), the composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` correspond (`hε`), and the
section invariant construction at the diagonal is preserved (`hL`), then the canonical
orientations `θ_f` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) over `Λ` and `Λ'`
correspond: `vω ≫ θ'_f = Ψ θ_f ≫ (Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d])`. The compatibility of the
smooth base change identifications, a hypothesis of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`, holds by
`AlgebraicGeometry.Etale.map_sectionInvariantDiagonalIso_hom_comp`. -/
theorem map_dualizingComplexTwistShiftIso_reduction (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsSeparated f]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ (pullback f f)] [HasInvertibleExponent Λ' (pullback f f)]
    (vω : (derivedExtendScalars hρ ha X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      (reductionSupportedCoefficientChange hρ ha τ).mapSupportedClass _
        ((reductionSupportedCoefficientChange hρ ha τ).tateShiftIso F.U d) (frameClass Λ F) =
          frameClass Λ' F)
    (hε : (derivedExtendScalars hρ ha X).map (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha X).hom =
      ((derivedExtendScalarsUpperShriekMap hρ ha (pullback.diagonal f)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f)^![Λ']).map
            (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω).hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' (pullback.fst f f)
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom)
    (hL : (reductionSupportedCoefficientChange hρ ha τ).PreservesSectionInvariantIso
      (pullback.diagonal f)) :
    (derivedExtendScalars hρ ha X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        ((reductionSupportedCoefficientChange hρ ha τ).twistShiftConstantComplexIso X d).hom =
      vω.hom ≫ (dualizingComplexTwistShiftIso Λ' f d aY).hom :=
  (reductionSupportedCoefficientChange hρ ha τ).map_dualizingComplexTwistShiftIso f d aY vω
    (derivedExtendScalarsDualizingComplexPullbackFstIso hρ ha f d vω) hframe
    (map_sectionInvariantDiagonalIso_hom_comp hρ ha f d vω) hε hL

end Etale

end AlgebraicGeometry
