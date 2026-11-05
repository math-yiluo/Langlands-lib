import Langlands.Geometry.Building.ChamberFiltration

/-!
# Transport of sharp chamber products to facets

The facet half of KP Corollary 7.4.9 follows from its chamber half and the
signed filtration comparisons of 6.3.21. The coordinate equivalences below
preserve every underlying rational point and the supplied factor order.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

section FacetTransport

variable
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    (hSys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {F C : Set D.Apartment} {x : D.Apartment} {ν : cocharacterLattice S}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    (hPos : D.FacetChamberPositiveSystem F C ν) (hx : x ∈ C)

include hAS4 hSys hC hFC hPos hx

/-- Positive facet blocks at depth `0` and negative facet blocks at depth
`0+` are exactly the chamber blocks at depth `0`. -/
theorem facetRootBlock_eq_chamberRootBlock_of_sign (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hpair : if strict then latticePairing S a ν < 0 else 0 < latticePairing S a ν) :
    D.facetRootBlock F strict a = D.chamberRootBlock x false a := by
  obtain ⟨-, hcomp⟩ :=
    D.chamberFacetRootFiltrationConclusion hAS4 hSys hC hFC hPos hx
  obtain ⟨-, -, -, hblock, hpos, hneg⟩ := hcomp a ha
  have h0 := (D.chamberRootFiltrationConclusion hAS4 hC hx a ha).1
  rw [hblock strict, D.chamberRootBlock_eq_rootGroup x false ha]
  cases strict with
  | false =>
    change (D.rootFixer a F : Set (rationalPoints G)) =
      (D.filtration x a 0 : Set (rationalPoints G))
    rw [hpos hpair, h0]
  | true =>
    change (D.rootFixerPlus a F : Set (rationalPoints G)) =
      (D.filtration x a 0 : Set (rationalPoints G))
    rw [hneg hpair, h0]

/-- The signed facet/chamber identification preserves the actual point,
including when the root block has a doubled-root factor. -/
def facetChamberRootBlockEquiv (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hpair : if strict then latticePairing S a ν < 0 else 0 < latticePairing S a ν) :
    D.facetRootBlock F strict a ≃ D.chamberRootBlock x false a :=
  Set.equivOfEq
    (D.facetRootBlock_eq_chamberRootBlock_of_sign hAS4 hSys hC hFC hPos hx strict ha hpair)

@[simp] theorem facetChamberRootBlockEquiv_coe (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hpair : if strict then latticePairing S a ν < 0 else 0 < latticePairing S a ν)
    (v : D.facetRootBlock F strict a) :
    (D.facetChamberRootBlockEquiv hAS4 hSys hC hFC hPos hx strict ha hpair v :
      rationalPoints G) = v :=
  rfl

/-- Coordinatewise transport of an ordered family of signed facet blocks
to the same chamber blocks, without reindexing. -/
def facetChamberBlockCoordinatesEquiv (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : ∀ j, a j ∈ relativeRoots i)
    (hpair : ∀ j,
      if strict then latticePairing S (a j) ν < 0 else 0 < latticePairing S (a j) ν) :
    (∀ j, D.facetRootBlock F strict (a j)) ≃
      (∀ j, D.chamberRootBlock x false (a j)) :=
  Equiv.piCongrRight fun j =>
    D.facetChamberRootBlockEquiv hAS4 hSys hC hFC hPos hx strict (ha j) (hpair j)

/-- The coordinate equivalence leaves the original ordered multiplication
map unchanged as a rational point. -/
theorem orderedFacetBlockProduct_eq_chamber (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : ∀ j, a j ∈ relativeRoots i)
    (hpair : ∀ j,
      if strict then latticePairing S (a j) ν < 0 else 0 < latticePairing S (a j) ν)
    (v : ∀ j, D.facetRootBlock F strict (a j)) :
    D.orderedFacetBlockProduct F strict a v =
      D.orderedChamberBlockProduct x false a
        (D.facetChamberBlockCoordinatesEquiv hAS4 hSys hC hFC hPos hx strict a ha hpair v) :=
  rfl

/-- The entire published sharp facet conclusion follows from the chamber
conclusion under the existing geometric sign condition. -/
theorem chamberSharpFacetConclusion_of_chamberSharpConclusion
    (hsharp : D.ChamberSharpConclusion C x ν) :
    D.ChamberSharpFacetConclusion F C x ν := by
  obtain ⟨hconst, hcomp⟩ :=
    D.chamberFacetRootFiltrationConclusion hAS4 hSys hC hFC hPos hx
  refine ⟨hconst, hcomp, ?_⟩
  intro nneg npos aneg apos hianeg hraneg hiapos hrapos
  have hnr (j : Fin nneg) : aneg j ∈ RelativeRoot.indivisiblePositiveRoots i (-ν) := by
    rw [← hraneg]
    exact Set.mem_range_self j
  have hpr (j : Fin npos) : apos j ∈ RelativeRoot.indivisiblePositiveRoots i ν := by
    rw [← hrapos]
    exact Set.mem_range_self j
  have hna (j : Fin nneg) : aneg j ∈ relativeRoots i := (hnr j).1.1
  have hpa (j : Fin npos) : apos j ∈ relativeRoots i := (hpr j).1.1
  have hnn (j : Fin nneg) : latticePairing S (aneg j) ν < 0 := by
    simpa using (hnr j).2
  have hpp (j : Fin npos) : 0 < latticePairing S (apos j) ν := (hpr j).2
  let en := D.facetChamberBlockCoordinatesEquiv hAS4 hSys hC hFC hPos hx
    true aneg hna hnn
  let ep := D.facetChamberBlockCoordinatesEquiv hAS4 hSys hC hFC hPos hx
    false apos hpa hpp
  let e := Equiv.prodCongr en (Equiv.prodCongr (Equiv.refl (D.sharpCentralizer {x})) ep)
  have hnEq : D.orderedFacetBlockProduct F true aneg =
      D.orderedChamberBlockProduct x false aneg ∘ en := rfl
  have hpEq : D.orderedFacetBlockProduct F false apos =
      D.orderedChamberBlockProduct x false apos ∘ ep := rfl
  have htEq : D.orderedSharpFacetProduct F x aneg apos =
      D.orderedSharpChamberProduct x false aneg apos ∘ e := rfl
  obtain ⟨hnI, hnR, hpI, hpR, htI, htR⟩ :=
    hsharp.2.2.2.2 false nneg npos aneg apos hianeg hraneg hiapos hrapos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnEq]
    exact hnI.comp en.injective
  · rw [hnEq, en.surjective.range_comp, hnR]
  · rw [hpEq]
    exact hpI.comp ep.injective
  · rw [hpEq, ep.surjective.range_comp, hpR]
  · rw [htEq]
    exact htI.comp e.injective
  · rw [htEq, e.surjective.range_comp, htR]

end FacetTransport

end Langlands.Geometry.Building.KPApartmentData
