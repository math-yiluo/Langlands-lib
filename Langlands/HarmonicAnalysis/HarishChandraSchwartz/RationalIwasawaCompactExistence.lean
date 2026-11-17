import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof
import Langlands.BruhatTits.Iwasawa.AvailableProof
import Langlands.BruhatTits.Iwasawa.ExistenceStatement
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.Representation.Aubert.General.StandardFamilyStructure

/-! # A compact open Iwasawa subgroup of `G(F)`

`RationalIwasawaCompactExistenceStatement` asserts that every connected reductive group
over a nonarchimedean local field has a maximal split torus `i`, a generic cocharacter `ν`
and a compact open subgroup `K` of `G(F)` with `G(F) = P₀(F) K`, where
`P₀(F) = standardParabolicPoints i ν ∅`. This is the structural choice that the published
analytic interfaces of Waldspurger VIII take as data (Waldspurger I.1 fixes such a `K`).

Two published global inputs imply it:

* `BruhatTitsAvailabilityStatement`, through the special compact subgroup at a special
  vertex of the assigned building datum (KP Theorem 5.3.4 via `availableIwasawa`);
* `BruhatTits.Iwasawa.IwasawaExistenceStatement`.

Neither input is proved in the Library; both theorems here are conditional.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

/-- **Existence of a compact open Iwasawa subgroup.** For every nonarchimedean local field
`F` and every affine, locally finite type connected reductive group scheme `G` over `F`,
there are a maximal split torus `i : S → G`, a generic cocharacter `ν` of `S` and a compact
open subgroup `K` of `G(F)` (canonical rational-point topology) such that every point of
`G(F)` is a product `p k` with `p` in the empty-index standard parabolic
`P₀(F) = standardParabolicPoints i ν ∅` and `k ∈ K`. -/
def RationalIwasawaCompactExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (ν : cocharacterLattice S) (K : OpenSubgroup (rationalPoints G)),
      IsMaximalSplitTorus i ∧ IsGenericCocharacter i ν ∧
        IsCompact (K : Set (rationalPoints G)) ∧
        IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup

/-- **Iwasawa compact existence from Bruhat–Tits availability.** The torus is the one of the
assigned building datum, `ν` is any generic cocharacter of it, and `K` is the special compact
subgroup at a special apartment vertex; `G(F) = P₀(F) K` is the literal product order of
KP Theorem 5.3.4 supplied by `availableIwasawa`. -/
theorem rationalIwasawaCompactExistence_of_bruhatTitsAvailability
    (hAv : BruhatTitsAvailabilityStatement.{u}) :
    RationalIwasawaCompactExistenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨𝔅, h𝔅⟩ := hAv
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  obtain ⟨ν, hν⟩ :=
    (𝔅.datum F G hG).base.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter
      (𝔅.datum F G hG).base.i
  obtain ⟨x, hx⟩ := availableSpecialVertexExistence F G hG 𝔅 hA
  obtain ⟨-, -, hP, hK⟩ :=
    (Langlands.BruhatTits.Iwasawa.availableIwasawa F G hG 𝔅 hA ν hν).1 x hx
  exact ⟨_, _, ν, ⟨_, hK.2.1⟩, (𝔅.datum F G hG).base.isMaximalSplitTorus, hν, hK.1,
    isIwasawaPair_of_pointProductEqualities (hP.2.2.1 ∅ (Set.empty_subset _))⟩

/-- **Iwasawa compact existence from `IwasawaExistenceStatement`.** Choose any maximal split
torus with a generic cocharacter; the special compact subgroup supplied for them by the
premise is compact open and its standard-parabolic product family contains `G(F) = P₀(F) K`. -/
theorem rationalIwasawaCompactExistence_of_iwasawaExistence
    (h : BruhatTits.Iwasawa.IwasawaExistenceStatement.{u}) :
    RationalIwasawaCompactExistenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨S, i, ν, hi, hν⟩ := RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  obtain ⟨_, D, _, _, _, _, x, _, hprops, _, hproducts, _⟩ := h F G hG S i hi ν hν
  exact ⟨S, i, ν, ⟨D.specialCompactSubgroup x, hprops.2.1.2.1⟩, hi, hν, hprops.2.1.1,
    isIwasawaPair_of_pointProductEqualities (hproducts.2.2.1 ∅ (Set.empty_subset _))⟩

end Langlands.HarishChandraSchwartz
