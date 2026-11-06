import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Derived.CentralSplitTorusProductSurjectivity
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Rational.DerivedCoverReflectionLift
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Actual central complements of compatible derived tori -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual central split torus supplementing a supplied derived-torus map. -/
structure DerivedTorusCentralComplement (e : T ⟶ S) (i : S.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  map : torus ⟶ S
  isSplit : IsSplitTorus torus.toGrp
  isCentral : IsCentral (CommGroupScheme.groupHom map ≫ i)
  flat : Flat (RelativeRoot.centralComplementProduct e map).hom.hom.left
  surjective : Surjective (RelativeRoot.centralComplementProduct e map).hom.hom.left

variable [IsAffineHom G.X.hom]
    (e : T ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G) (d : D ⟶ G)
    {J : Type v} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}

/-- A supplied actual root datum forces the Weyl norm to be central, and gives
an actual flat-surjective central complement for compatible maximal split tori. -/
theorem exists_derivedTorusCentralComplement
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hi : IsMaximalSplitTorus i) (hj : IsMaximalSplitTorus j)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hP : IsRootDatumOf i P) : Nonempty (DerivedTorusCentralComplement e i) := by
  have : Mono i.hom.hom.left := hi.1.mono
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  obtain ⟨c, hc⟩ := hi.exists_factor_of_commute ha.1.1.1 a (ha.1.2.commute_values i)
  let c' : A ⟶ S := Additive.ofMul c
  have hc' : CommGroupScheme.groupHom c' ≫ i = a := hc
  have hnorm : IsCentral (CommGroupScheme.groupHom (relativeWeylTorusNorm i) ≫ i) := by
    apply isCentral_of_forall_cocharacter hi.1.1
    intro ν
    have h := hP.relativeRootReflectionData.weylSum_mem_centralCocharacters i hi.1.1 ν
    rw [mem_centralCocharacters, ← comp_relativeWeylTorusNorm] at h
    exact h
  have hsurj : Surjective (RelativeRoot.centralComplementProduct e c').hom.hom.left :=
    splitProduct_surjective_of_central_weyl_norm hd hi.1 hj hsquare ha hc' hnorm
  have : Surjective (RelativeRoot.centralComplementProduct e c').hom.hom.left := hsurj
  have : IsAffineHom (T.toGrp ⊗ A.toGrp).X.hom := (hj.1.1.tensor ha.1.1.1).isAffineHom
  have : Smooth (T.toGrp ⊗ A.toGrp).X.hom := (hj.1.1.tensor ha.1.1.1).smooth
  have : Smooth S.X.hom := hi.1.1.smooth
  refine ⟨⟨A, c', ha.1.1.1, ?_, flat_of_surjective _, hsurj⟩⟩
  rw [hc']
  exact ha.1.2

/-- Choose the actual central complement constructed from the supplied datum. -/
def derivedTorusCentralComplement
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hi : IsMaximalSplitTorus i) (hj : IsMaximalSplitTorus j)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hP : IsRootDatumOf i P) : DerivedTorusCentralComplement e i :=
  Classical.choice (exists_derivedTorusCentralComplement e j i d hG hd hi hj hsquare hP)

end Langlands.GroupScheme
