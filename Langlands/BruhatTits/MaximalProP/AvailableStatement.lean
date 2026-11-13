import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Cohomology.DivisibleSystem.ProPInvariants

/-! # Maximal open pro-`p` subgroups on available Bruhat–Tits data (corrected KP 13.5.2) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.MaximalProP

section Maximal

variable {X : Type*} [Group X] [TopologicalSpace X]

/-- `H` is a maximal open pro-`p` subgroup of `A`: an open pro-`p` subgroup of `X` contained
in `A` that is contained in no other open pro-`p` subgroup of `X` lying in `A`. -/
def IsMaximalOpenProPIn (p : ℕ) (A H : Subgroup X) : Prop :=
  H ≤ A ∧ IsOpen (H : Set X) ∧ Langlands.Cohomology.IsProPSubgroup p H ∧
    ∀ H' : Subgroup X, H ≤ H' → H' ≤ A → IsOpen (H' : Set X) →
      Langlands.Cohomology.IsProPSubgroup p H' → H' = H

end Maximal

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The subgroup `G(F)_{F,0+}` of a facet `F` of `B(G)`: the generic points of the integral
sections of the neutral facet model whose reduction lies in the residue-field points of the
supplied radical of its special fibre (KP Axiom 4.1.22(7), Corollary 8.4.12). -/
def facetPositiveSubgroup (D : KPBuildingDatum G)
    (Fa : BuildingFacet D.base.toValuationBuildingData) : Subgroup (rationalPoints G) :=
  (D.quotients.quotient Fa).positivePoints

/-- The subgroup `G(F)^0_F` of a facet `F` of `B(G)`: its pointwise fixer in `G(F)^0`. For a
chamber this is the Iwahori subgroup of KP Definition 7.4.5 under the axioms. -/
def facetZeroFixer (D : KPBuildingDatum G)
    (Fa : BuildingFacet D.base.toValuationBuildingData) : Subgroup (rationalPoints G) :=
  BuildingModelFamily.zeroFixer D.base (BuildingModelIndex.ofFacet Fa)

/-- The four conclusions of corrected KP Proposition 13.5.2 for the data `D`, with the point
topology of `G(F)` and `p` the characteristic of the residue field of `F`:

1. every `G(F)_{F,0+}` is an open pro-`p` subgroup of `G(F)^0`;
2. it is a maximal open pro-`p` subgroup of `G(F)^0` exactly when `F` is a chamber;
3. every maximal open pro-`p` subgroup of `G(F)^0` is `G(F)_{C,0+}` for a chamber `C`;
4. for a chamber `C`, the normalizer of `G(F)_{C,0+}` in `G(F)^0` is `G(F)^0_C`. -/
def MaximalProPConclusions (D : KPBuildingDatum G) : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  (∀ Fa : BuildingFacet D.base.toValuationBuildingData,
    facetPositiveSubgroup D Fa ≤ D.base.zeroSubgroup ∧
      IsOpen (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ∧
      Langlands.Cohomology.IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa)) ∧
  (∀ Fa : BuildingFacet D.base.toValuationBuildingData,
    IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup (facetPositiveSubgroup D Fa) ↔
      D.base.IsChamber Fa.val) ∧
  (∀ H : Subgroup (rationalPoints G),
    IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H →
      ∃ C : BuildingFacet D.base.toValuationBuildingData,
        D.base.IsChamber C.val ∧ H = facetPositiveSubgroup D C) ∧
  (∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
    Subgroup.normalizer (facetPositiveSubgroup D C : Set (rationalPoints G)) ⊓
        D.base.zeroSubgroup =
      facetZeroFixer D C)

/-- Corrected KP Proposition 13.5.2 for every connected reductive group over every
nonarchimedean local field, under the full corrected Definition 4.1.26. -/
def AvailableMaximalProPStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      MaximalProPConclusions (𝔅.datum F G hG)

end Langlands.BruhatTits.MaximalProP
