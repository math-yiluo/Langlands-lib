import Langlands.GroupScheme.Rational.DerivedCoverUnipotentLift
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # Contracting-point lifts from actual relative-root reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace RelativeRootReflectionData

variable [Fintype (relativeWeylGroup i)] (R : RelativeRootReflectionData i)

include R

/-- Integral normalizer reflection data force the Weyl sum to annihilate each
actual root, without generating the relative Weyl group. -/
theorem latticePairing_weylSum_eq_zero
    (ν : cocharacterLattice T) (α : characterLattice T) (hα : α ∈ relativeRoots i) :
    latticePairing T α (relativeWeylCocharacterSum i ν) = 0 := by
  let a : relativeRoots i := ⟨α, hα⟩
  have hself : weylAction i (R.representative a) α = -α := by
    rw [R.action]
    change α - latticePairing T a.val (R.coroot a) • α = -α
    rw [R.pair_self, two_zsmul]
    abel
  have h := latticePairing_relativeWeyl i
    (QuotientGroup.mk (R.representative a)) α (relativeWeylCocharacterSum i ν)
  rw [relativeWeylCharacterAction_mk, hself, relativeWeylCocharacterSum_fixed,
    map_neg, LinearMap.neg_apply] at h
  omega

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Actual integral reflection data make the Weyl sum central on every test
scheme. A full relative-root-system realization is unnecessary. -/
theorem weylSum_mem_centralCocharacters
    (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T) :
    relativeWeylCocharacterSum i ν ∈ centralCocharacters i :=
  rootAnnihilatorCentrality k G T hT i _ fun α hα =>
    R.latticePairing_weylSum_eq_zero i ν α hα

end RelativeRootReflectionData

namespace Dynamic

/-- Actual root-reflection existence alone suffices for contracting-point lifts
at a maximal split torus; Weyl finiteness follows from reductivity. -/
theorem exists_derivedCover_lift_of_mem_unipotent_of_reflections
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (ν : cocharacterLattice T) (g : rationalPoints G)
    (hg : g ∈ (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g := by
  let : Finite (relativeWeylGroup i) :=
    hcover.isConnectedReductive.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hcover.isConnectedReductive.connectedSpace
  exact exists_derivedCover_lift_of_mem_unipotent_of_central_weylSum i hcover ν
    (relativeWeylCocharacterSum_mem_centralCocharacters i hi.isSplitSubtorus.1 href ν) g hg

/-- Supplied integral reflection data give the same lifts, without constructing
or identifying an abstract Weyl group. -/
theorem exists_derivedCover_lift_of_mem_unipotent_of_reflectionData
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (R : RelativeRootReflectionData i)
    (ν : cocharacterLattice T) (g : rationalPoints G)
    (hg : g ∈ (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g := by
  let : Finite (relativeWeylGroup i) :=
    hcover.isConnectedReductive.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hcover.isConnectedReductive.connectedSpace
  exact exists_derivedCover_lift_of_mem_unipotent_of_central_weylSum i hcover ν
    (R.weylSum_mem_centralCocharacters i hi.isSplitSubtorus.1 ν) g hg

/-- All contracting rational points belong to the actual cover image when
actual relative-root reflections exist. -/
theorem unipotentPoints_le_derivedCoverImage_of_reflections
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (ν : cocharacterLattice T) :
    (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤
      (rationalPoints.map (π ≫ d)).range := by
  intro g hg
  exact exists_derivedCover_lift_of_mem_unipotent_of_reflections
    i hcover hi href ν g hg

/-- Supplied integral reflection data put the full contracting rational
subgroup in the actual cover image. -/
theorem unipotentPoints_le_derivedCoverImage_of_reflectionData
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (R : RelativeRootReflectionData i) (ν : cocharacterLattice T) :
    (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤
      (rationalPoints.map (π ≫ d)).range := by
  intro g hg
  exact exists_derivedCover_lift_of_mem_unipotent_of_reflectionData
    i hcover hi R ν g hg

/-- Choose an actual cover point over each contracting rational point, using
only the existence of actual relative-root reflections. -/
def derivedCoverUnipotentPointLiftOfReflections
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (ν : cocharacterLattice T)
    (g : (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    rationalPoints C :=
  (exists_derivedCover_lift_of_mem_unipotent_of_reflections
    i hcover hi href ν g.val g.property).choose

/-- The selected cover point maps to the original contracting point under the
literal composite of the supplied cover and derived inclusion. -/
theorem derivedCoverUnipotentPointLiftOfReflections_comp
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (ν : cocharacterLattice T)
    (g : (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    rationalPoints.map (π ≫ d)
        (derivedCoverUnipotentPointLiftOfReflections i hcover hi href ν g) = g.val :=
  (exists_derivedCover_lift_of_mem_unipotent_of_reflections
    i hcover hi href ν g.val g.property).choose_spec

end Dynamic

end Langlands.GroupScheme
