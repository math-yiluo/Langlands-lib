import Langlands.GroupScheme.Reductive.SplitIsogenyLocalLevis
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphReductive

/-! # Actual graphs of local reductive isogenies over a prescribed torus map -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual cocharacter centralizers with an isogeny over the prescribed torus map.
The source and target tori and cocharacters need not coincide. -/
structure LocalIsogeny (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (t : T ⟶ T')
    (ν : cocharacterLattice T) (ν' : cocharacterLattice T') where
  left : GroupScheme (Spec (CommRingCat.of k))
  right : GroupScheme (Spec (CommRingCat.of k))
  leftInclusion : left ⟶ G
  rightInclusion : right ⟶ G'
  leftClosed : IsClosedSubgroup leftInclusion
  rightClosed : IsClosedSubgroup rightInclusion
  leftRep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
    leftInclusion
  rightRep : (Dynamic.centralizer (CommGroupScheme.groupHom ν' ≫ i')).IsRepresentedBy
    rightInclusion
  leftTorus : T.toGrp ⟶ left
  rightTorus : T'.toGrp ⟶ right
  leftTorusComp : leftTorus ≫ leftInclusion = i
  rightTorusComp : rightTorus ≫ rightInclusion = i'
  hom : left ⟶ right
  isogeny : IsIsogeny hom
  torusComp : leftTorus ≫ hom = CommGroupScheme.groupHom t ≫ rightTorus

open Langlands.LinearAlgebra in
/-- Choose the existing affine centralizers and realize the restricted root-datum
isogeny on them. All geometric data come from the given reductive groups. -/
def localIsogeny
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; LeviGluing.IsRankOneDirection i ν) :
    LocalIsogeny i i' (torusMap hT' f) ν (f.coweightMap ν) := by
  let := hG.isAffineHom
  let := hG'.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  let z := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ν ≫ i)
  let z' := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom (f.coweightMap ν) ≫ i')
  have hz := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ν ≫ i)
  have hz' := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom (f.coweightMap ν) ≫ i')
  let j := Dynamic.torusFactor i (CommGroupScheme.groupHom ν) hz
  let j' := Dynamic.torusFactor i' (CommGroupScheme.groupHom (f.coweightMap ν)) hz'
  have hj : j ≫ z = i := Dynamic.torusFactor_comp _ _ _
  have hj' : j' ≫ z' = i' := Dynamic.torusFactor_comp _ _ _
  have hex := exists_centralizer_isogeny hG hG' hT hT' i i' hi hi' hP hP' f ν hν
    z z' (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom _) hz hz' j j' hj hj'
  exact
    { left := _
      right := _
      leftInclusion := z
      rightInclusion := z'
      leftClosed := Dynamic.Affine.isClosedSubgroup_centralizerHom _
      rightClosed := Dynamic.Affine.isClosedSubgroup_centralizerHom _
      leftRep := hz
      rightRep := hz'
      leftTorus := j
      rightTorus := j'
      leftTorusComp := hj
      rightTorusComp := hj'
      hom := hex.choose
      isogeny := hex.choose_spec.1
      torusComp := hex.choose_spec.2 }

namespace LocalIsogeny

variable {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : cocharacterLattice T} {ν' : cocharacterLattice T'}
    (C : LocalIsogeny i i' t ν ν')

instance [IsAffineHom G.X.hom] : IsAffineHom C.left.X.hom := C.leftClosed.isAffineHom
instance [IsAffineHom G'.X.hom] : IsAffineHom C.right.X.hom := C.rightClosed.isAffineHom

instance [Smooth G.X.hom] [IsAffineHom G.X.hom] : Smooth C.left.X.hom :=
  (dynamicSmooth k G _ _ C.leftInclusion).2.1 C.leftRep

instance [Smooth G'.X.hom] [IsAffineHom G'.X.hom] : Smooth C.right.X.hom :=
  (dynamicSmooth k G' _ _ C.rightInclusion).2.1 C.rightRep

instance [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    ConnectedSpace C.left.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G _ C.leftRep

instance [Smooth G'.X.hom] [IsAffineHom G'.X.hom] [ConnectedSpace G'.X.left] :
    ConnectedSpace C.right.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G' _ C.rightRep

theorem leftTorus_closed (hi : IsClosedSubgroup i) : IsClosedSubgroup C.leftTorus :=
  IsClosedSubgroup.of_comp C.leftClosed (by rw [C.leftTorusComp]; exact hi)

theorem rightTorus_closed (hi : IsClosedSubgroup i') : IsClosedSubgroup C.rightTorus :=
  IsClosedSubgroup.of_comp C.rightClosed (by rw [C.rightTorusComp]; exact hi)

end LocalIsogeny

section Family

variable {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    (C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j))

/-- Source centralizers of the local-isogeny family. -/
abbrev localGroups : I → GroupScheme (Spec (CommRingCat.of k)) := fun j => (C j).left

/-- The first maps retain the actual source centralizer inclusions. -/
abbrev localFirst : ∀ j, localGroups C j ⟶ G := fun j => (C j).leftInclusion

/-- The second maps use the actual, possibly inseparable, local isogenies. -/
abbrev localSecond : ∀ j, localGroups C j ⟶ G' :=
  fun j => (C j).hom ≫ (C j).rightInclusion

/-- The generated graph, with the graph of the prescribed torus map included. -/
abbrev LocalIsogenyGraphEnvelope :=
  LeviGluing.GraphEnvelope (T := T.toGrp) (localGroups C) (localFirst C) (localSecond C)
    i (CommGroupScheme.groupHom t ≫ i')

/-- Construct the actual smooth connected affine graph from the local isogenies. -/
def localIsogenyGraphEnvelope
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom]
    (hT : IsSplitTorus T.toGrp) : LocalIsogenyGraphEnvelope C :=
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  LeviGluing.graphEnvelope _ _ _ _ _ fun _ => ⟨inferInstance, inferInstance, inferInstance⟩

namespace LocalIsogenyGraphEnvelope

variable {C} (D : LocalIsogenyGraphEnvelope C)

/-- Each local source torus factor is the distinguished graph torus. -/
@[reassoc (attr := simp)]
theorem leftTorus_localLift (j : I) : (C j).leftTorus ≫ D.localLift j = D.torusLift :=
  D.local_torusLift j (C j).leftTorus (C j).leftTorusComp (by
    change (C j).leftTorus ≫ (C j).hom ≫ (C j).rightInclusion = _
    rw [← Category.assoc, (C j).torusComp, Category.assoc, (C j).rightTorusComp])

/-- The first projection contains each full source centralizer, on every test. -/
theorem localFirst_le_range (j : I) :
    SubgroupFunctor.range (C j).leftInclusion ≤ SubgroupFunctor.range D.first := by
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (D.localLift j).hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom, D.localLift_first]⟩

/-- The source torus is contained in the first projection on every test. -/
theorem torus_le_range_first : SubgroupFunctor.range i ≤ SubgroupFunctor.range D.first := by
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ D.torusLift.hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom, D.torusLift_first]⟩

/-- A source root annihilating a local direction is contained in the first projection. -/
theorem root_le_range_first (j : I) (α : characterLattice T)
    (hα : latticePairing T α (ν j) = 0) :
    RelativeRoot.subgroup i α ≤ SubgroupFunctor.range D.first := by
  apply (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i α (ν j) hα).trans
  rw [← (C j).leftRep.2]
  exact D.localFirst_le_range j

/-- The first projection is faithfully flat whenever the chosen local directions
cover the simple roots of one generic chamber. -/
theorem first_geometry
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (ζ : cocharacterLattice T) (hζ : IsGenericCocharacter i ζ)
    (hcover : ∀ α ∈ simpleRelativeRoots i ζ, ∃ j, latticePairing T α (ν j) = 0)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) = SubgroupFunctor.range i) :
    Flat D.first.hom.hom.left ∧ Surjective D.first.hom.hom.left ∧
      LocallyOfFinitePresentation D.first.hom.hom.left ∧ QuasiCompact D.first.hom.hom.left := by
  exact LeviGluing.projection_geometry_of_contains_simpleRootLevis hT hi hP hζ D.first
    (fun α hα => by obtain ⟨j, hj⟩ := hcover α hα; exact D.root_le_range_first j α hj)
    (fun α hα => by
      obtain ⟨j, hj⟩ := hcover α hα
      apply D.root_le_range_first j (-α)
      simp only [map_neg, LinearMap.neg_apply, hj, neg_zero])
    (by rw [hZ]; exact D.torus_le_range_first)

end LocalIsogenyGraphEnvelope
end Family

end Langlands.GroupScheme.RootDatumIsogenyRealization
