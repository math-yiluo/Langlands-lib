import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.Geometry.Building.KPEnlargedBuilding
import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.Galois.Local.SeparableUnramifiedStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero

/-!
# Torus regression examples for KP building data

Propositions about a torus `T` over a nonarchimedean local field `F` and every
`D : KPBuildingDatum T` satisfying `D.SatisfiesGroupAxioms`. They keep apart the reduced
building and the enlarged building `B(T) × CentralFactor T`, and the three subgroups
`T(F)^0 ≤ T(F)^1 ≤ T(F)`. Here `T(F)^0` is the image in `T(F)` of the Library's
`D.base.centralizerZero` (KP Definitions 2.5.13 and 2.6.23) and `T(F)^1` is
`rationalCommonNormKernel T` (KP Proposition 2.5.8).

* `KPTorusBuildingStatement`: every torus.
* `KPSplitTorusBuildingStatement`: split tori.
* `KPAnisotropicTorusStatement`: anisotropic tori.
* `KPUnramifiedNormOneTorusStatement` and `KPRamifiedNormOneTorusStatement`: the norm-one
  torus of a quadratic extension inside `SeparableClosure F`.
* `KPTorusRegressionStatement`: the conjunction of the five.

The affine structure morphism that `KPBuildingDatum T` needs is derived from the torus
hypothesis (`IsTorus.isRelativeTorus`, `RelativeTorus.IsTorus.isAffineHom`) or, for norm-one
tori, supplied by the instance `WeilGm.normOne_isAffineHom`; it is not an extra premise.

This file states the propositions and proves none of them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

/-- Every torus `T` over a nonarchimedean local field `F`. The real vector space
`CentralFactor T` of the enlarged building is finite-dimensional of dimension the `F`-split
rank of `T`. For every `D : KPBuildingDatum T` satisfying the one-group axioms: the reduced
building has exactly one point; the enlarged building has exactly one point if and only if
`T` is anisotropic; there is exactly one facet; `T(F)^0 ≤ T(F)^1`; at the facet the parahoric
`D.parahoric x` is `T(F)^0`; at every point the compact stabilizer is `T(F)^1` and the full
stabilizer is `T(F)`; every point of the enlarged building has stabilizer `T(F)^1`. -/
def KPTorusBuildingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T),
      letI : IsAffineHom T.X.hom := hT.isRelativeTorus.isAffineHom
      (FiniteDimensional ℝ (CentralFactor T) ∧
        (Module.finrank ℝ (CentralFactor T) : ℕ∞) = splitRank T) ∧
      ∀ D : KPBuildingDatum T, D.SatisfiesGroupAxioms →
        let B := D.base.toValuationBuildingData
        let T0 : Subgroup (rationalPoints T) :=
          D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j)
        Nonempty (Unique B.ReducedBuilding) ∧
        (Nonempty (Unique B.EnlargedBuilding) ↔ IsAnisotropic T) ∧
        Nonempty (Unique (BuildingFacet B)) ∧
        T0 ≤ rationalCommonNormKernel T ∧
        (∀ x : BuildingFacet B, D.parahoric x = T0) ∧
        (∀ y : B.ReducedBuilding,
          B.compactStabilizer y = rationalCommonNormKernel T ∧ B.fixer y = ⊤) ∧
        ∀ z : B.EnlargedBuilding, B.enlargedStabilizer z = rationalCommonNormKernel T

/-- A split torus `T` of rank `N` over a nonarchimedean local field `F`, with residue field
of cardinality `q`, and every `D : KPBuildingDatum T` satisfying the one-group axioms:
`T(F)^0 = T(F)^1`; `T(F)^0` is normal and the valuation homomorphism, followed by an
identification of `Hom(X^*_F(T), ℤ)` with `ℤ^N`, induces `T(F)/T(F)^0 ≃ ℤ^N`; and at the facet
the finite group of residue-field points of the reductive quotient has `(q - 1)^N`
elements. -/
def KPSplitTorusBuildingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of F))) (N : ℕ) (hT : IsSplitTorus T),
      splitRank T = N →
      letI : IsAffineHom T.X.hom := (RelativeTorus.IsTorus.of_isSplitTorus hT).isAffineHom
      ∀ (D : KPBuildingDatum T) (hD : D.SatisfiesGroupAxioms),
        let T0 : Subgroup (rationalPoints T) :=
          D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j)
        T0 = rationalCommonNormKernel T ∧
        (∃ hN : T0.Normal,
          letI : T0.Normal := hN
          ∃ (e : (rationalCharacters T →+ ℤ) ≃+ (Fin N → ℤ))
            (φ : rationalPoints T ⧸ T0 ≃* Multiplicative (Fin N → ℤ)),
            ∀ t : rationalPoints T,
              φ (t : rationalPoints T ⧸ T0) =
                Multiplicative.ofAdd (e (rationalCharacterValuation T t).toAdd)) ∧
        ∀ x : BuildingFacet D.base.toValuationBuildingData,
          Nat.card (D.finiteReductiveQuotientGroup x hD) = (Nat.card 𝓀[F] - 1) ^ N

/-- An anisotropic torus `T` over a nonarchimedean local field `F`: `T(F)^1 = T(F)`; `T(F)` is
compact in the canonical topology `rationalPointTopology F T.X`; and for every
`D : KPBuildingDatum T` satisfying the one-group axioms every point of the enlarged building
is fixed by all of `T(F)`. -/
def KPAnisotropicTorusStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T),
      IsAnisotropic T →
      letI : IsAffineHom T.X.hom := hT.isRelativeTorus.isAffineHom
      letI : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
      letI : TopologicalSpace (rationalPoints T) := rationalPointTopology F T.X
      rationalCommonNormKernel T = ⊤ ∧
      IsCompact (Set.univ : Set (rationalPoints T)) ∧
      ∀ D : KPBuildingDatum T, D.SatisfiesGroupAxioms →
        ∀ z : D.base.toValuationBuildingData.EnlargedBuilding,
          D.base.toValuationBuildingData.enlargedStabilizer z = ⊤

/-- The norm-one torus `T = R¹_{E/F} 𝔾_m` of an unramified quadratic extension `E/F` inside
`SeparableClosure F`, and every `D : KPBuildingDatum T` satisfying the one-group axioms:
`T(F)^0 = T(F)`, and at the facet the finite group of residue-field points of the reductive
quotient has `q + 1` elements, `q` the cardinality of the residue field of `F`. -/
def KPUnramifiedNormOneTorusStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E],
    Module.finrank F E = 2 → LocalGalois.Separable.ArithmeticUnramified F E →
      ∀ (D : KPBuildingDatum (WeilGm.normOne (CommRingCat.of F) E))
        (hD : D.SatisfiesGroupAxioms),
        D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j) = ⊤ ∧
        ∀ x : BuildingFacet D.base.toValuationBuildingData,
          Nat.card (D.finiteReductiveQuotientGroup x hD) = Nat.card 𝓀[F] + 1

/-- The norm-one torus `T = R¹_{E/F} 𝔾_m` of a ramified quadratic extension `E/F` inside
`SeparableClosure F`, in every residue characteristic, and every `D : KPBuildingDatum T`
satisfying the one-group axioms: `T(F)^1 = T(F)` and `T(F)^0` has index `2` in `T(F)`. -/
def KPRamifiedNormOneTorusStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E],
    Module.finrank F E = 2 → ¬ LocalGalois.Separable.ArithmeticUnramified F E →
      ∀ D : KPBuildingDatum (WeilGm.normOne (CommRingCat.of F) E),
        D.SatisfiesGroupAxioms →
          rationalCommonNormKernel (WeilGm.normOne (CommRingCat.of F) E) = ⊤ ∧
          (D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j)).index = 2

/-- The five torus regression examples together: `KPTorusBuildingStatement`,
`KPSplitTorusBuildingStatement`, `KPAnisotropicTorusStatement`,
`KPUnramifiedNormOneTorusStatement` and `KPRamifiedNormOneTorusStatement`. -/
def KPTorusRegressionStatement : Prop :=
  KPTorusBuildingStatement.{u} ∧ KPSplitTorusBuildingStatement.{u} ∧
    KPAnisotropicTorusStatement.{u} ∧ KPUnramifiedNormOneTorusStatement.{u} ∧
    KPRamifiedNormOneTorusStatement.{u}

end Langlands.Geometry.Building
