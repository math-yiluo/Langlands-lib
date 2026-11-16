import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleLocusOpenDescent
import Langlands.GroupScheme.Reductive.IdentityComponentLocusLiftingReduction

/-! # Semisimple-locus openness from affine torus neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance semisimpleLift_smooth_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance semisimpleLift_affine_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- The affine local input for descent, expressed using the actual self-centralizing torus. -/
def IdentityComponentSemisimpleAffineNeighbourhoodStatement : Prop :=
  ∀ {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (_hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of r)) (_hs : s ∈ identityComponentSemisimpleLocus G)
    (_hself : s ∈ splitTorus.geometricSelfCentralizingTorusLocus I G i),
      ∃ U : Set (Spec (CommRingCat.of r)), IsOpen U ∧ s ∈ U ∧
        U ⊆ identityComponentSemisimpleLocus G

namespace splitTorus

/-- Package the affine good-open input as an actual open neighbourhood. -/
def identityComponentSemisimpleNeighbourhood_of_selfCentralizing
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of r)) (hs : s ∈ identityComponentSemisimpleLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    IdentityComponentSemisimpleOpenNeighbourhood G s :=
  Classical.choice <| by
    obtain ⟨U, hU, hsU, hss⟩ := hAffine I G i hi s hs hself
    exact ⟨⟨⟨U, hU⟩, hsU, hss⟩⟩

/-- An algebraically closed maximal field fibre supplies the self-centralizing input. -/
def identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_intrinsic
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] [IsAlgClosed k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus G)
    (hmax : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)) :
    IdentityComponentSemisimpleOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
  have hred : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G :=
    (show IsSemisimple _ from hs).isConnectedReductive
  exact identityComponentSemisimpleNeighbourhood_of_selfCentralizing hAffine I G i hi _ hs
    (mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint I G i
      (fun k _ _ G hG T j hj => maximalTorusCentralizer k G hG T j hj) hi b hred hmax)

set_option maxHeartbeats 600000 in
/-- The affine good-open constructor extends a supplied maximal field-point
fibre to its algebraic closure before testing actual zero weights. -/
def identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_extension_intrinsic
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme _ I)) ((baseChange b).map i)) :
    IdentityComponentSemisimpleOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
  have hcm : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ I))
      (T' := commGroupScheme _ I) (baseChangeIso b I).symm hmax
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let d := q ≫ b
  have hd : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i d) :=
    isMaximalTorus_fieldPoint_extension I G i b hcm
  have hpoint : d (IsLocalRing.closedPoint (AlgebraicClosure k)) =
      b (IsLocalRing.closedPoint k) := by
    change b (q (IsLocalRing.closedPoint (AlgebraicClosure k))) = _
    rw [Subsingleton.elim (q (IsLocalRing.closedPoint (AlgebraicClosure k)))
      (IsLocalRing.closedPoint k)]
  have hs' : d (IsLocalRing.closedPoint (AlgebraicClosure k)) ∈
      identityComponentSemisimpleLocus G := by rwa [hpoint]
  have result := identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_intrinsic hAffine I G i
    hi d hs' hd
  simpa only [hpoint] using result

set_option maxHeartbeats 600000 in
/-- A closed standard torus over any base gives a good neighbourhood at a
field-valued point where its actual fibre is maximal. The field need not
be algebraically closed. -/
def identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_overScheme_intrinsic
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus S I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme S I)) ((baseChange b).map i)) :
    IdentityComponentSemisimpleOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
  classical
  let j := S.affineOpenCover.idx (b (IsLocalRing.closedPoint k))
  let A := S.affineOpenCover.X j
  let a : Spec A ⟶ S := S.affineOpenCover.f j
  have hrange : Set.range b ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint k)]
    exact S.affineOpenCover.covers (b (IsLocalRing.closedPoint k))
  let c : Spec (CommRingCat.of k) ⟶ Spec A := IsOpenImmersion.lift a b hrange
  have hc : c ≫ a = b := IsOpenImmersion.lift_fac a b hrange
  let H := (baseChange a).obj G
  let iA : splitTorus (Spec A) I ⟶ H := (baseChangeIso a I).inv ≫ (baseChange a).map i
  have hiA : IsClosedSubgroup iA :=
    (hi.baseChange a).iso_comp (baseChangeIso a I).symm
  have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange c).obj
      (commGroupScheme (Spec A) I)) ((baseChange c).map iA) :=
    isMaximalTorus_baseChangedHom_comp I G i a c (by rw [hc]; exact hmax)
  have hpoint : a (c (IsLocalRing.closedPoint k)) = b (IsLocalRing.closedPoint k) :=
    congrArg (fun f => f (IsLocalRing.closedPoint k)) hc
  have hsA : c (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus H := by
    rw [identityComponentSemisimpleLocus_baseChange]
    change a (c (IsLocalRing.closedPoint k)) ∈ identityComponentSemisimpleLocus G
    rwa [hpoint]
  let good := identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_extension_intrinsic hAffine
    I H iA hiA c hsA hm
  have result := identityComponentSemisimpleOpenNeighbourhood_of_openMap G a a.isOpenMap
    (c (IsLocalRing.closedPoint k)) good.neighbourhood.isOpen
    good.mem_neighbourhood good.subset_locus
  simpa only [hpoint] using result

end splitTorus

/-- A split presentation of the supplied actual commutative relative torus
reduces its good-open construction to standard-torus coordinates. -/
def identityComponentSemisimpleNeighbourhood_of_splitTorus_fieldPoint_intrinsic
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme S) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i)) :
    IdentityComponentSemisimpleOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) :=
  Classical.choice <| by
    classical
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let : Fintype I := Fintype.ofFinite I
    let j : splitTorus S I ⟶ G := e.inv ≫ i
    have hj : IsClosedSubgroup j := hi.iso_comp e.symm
    have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
        (splitTorus.commGroupScheme S I)) ((baseChange b).map j) := by
      have hm := IsMaximalTorus.iso_comp
        (T := (CommGroupScheme.baseChange b).obj T)
        (T' := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme S I))
        ((baseChange b).mapIso e.symm) hmax
      simpa only [j, Functor.map_comp, Functor.mapIso_hom, Iso.symm_hom] using hm
    exact ⟨splitTorus.identityComponentSemisimpleNeighbourhood_of_maximal_fieldPoint_overScheme_intrinsic hAffine
      I G j hj b hs hm⟩

/-- A specified split maximal torus in the actual residue fibre gives a good
original-base open through the retained actual lifting statement. -/
def identityComponentSemisimpleNeighbourhood_of_splitMaximalResidueTorus_intrinsic
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    (hLift : RelativeSplitTorusLiftingStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (hs : s ∈ identityComponentSemisimpleLocus G)
    (T₀ : CommGroupScheme (Spec (S.residueField s))) (hT₀ : IsSplitTorus T₀.toGrp)
    (i₀ : T₀.toGrp ⟶ (baseChange (S.fromSpecResidueField s)).obj G)
    (hmax : IsMaximalTorus (T := T₀) i₀) :
    IdentityComponentSemisimpleOpenNeighbourhood G s :=
  Classical.choice <| by
    obtain ⟨U, p, hp, b, hb, T, hT, i, hi, e, he⟩ :=
      hLift S G s T₀.toGrp hT₀ i₀ hmax.2.1
    let : Etale p := hp
    let TC : CommGroupScheme U := { T with comm := hT.isCommMonObj }
    have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj TC)
        ((baseChange b).map i) :=
      isMaximalTorus_of_lifting_recovery G s p b hb TC T₀ i i₀ e he hmax
    have hpoint : p (b (IsLocalRing.closedPoint (S.residueField s))) = s := by
      calc
        _ = S.fromSpecResidueField s (IsLocalRing.closedPoint (S.residueField s)) :=
          congrArg (fun f => f (IsLocalRing.closedPoint (S.residueField s))) hb
        _ = s := Scheme.fromSpecResidueField_apply _ _
    have hsU : b (IsLocalRing.closedPoint (S.residueField s)) ∈
        identityComponentSemisimpleLocus ((baseChange p).obj G) := by
      rw [identityComponentSemisimpleLocus_baseChange]
      change p (b (IsLocalRing.closedPoint (S.residueField s))) ∈
        identityComponentSemisimpleLocus G
      rwa [hpoint]
    let good := identityComponentSemisimpleNeighbourhood_of_splitTorus_fieldPoint_intrinsic hAffine
      ((baseChange p).obj G) TC hT i hi b hsU hm
    have result := identityComponentSemisimpleOpenNeighbourhood_of_openMap G p p.isOpenMap
      (b (IsLocalRing.closedPoint (S.residueField s))) good.neighbourhood.isOpen
      good.mem_neighbourhood good.subset_locus
    exact ⟨by simpa only [hpoint] using result⟩

/-- Construct the initial torus after a finite Galois residue extension,
then lift it and descend an actual good open to the original point. -/
def identityComponentSemisimpleNeighbourhood_of_lifting
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    (hLift : RelativeSplitTorusLiftingStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (hs : s ∈ identityComponentSemisimpleLocus G) :
    IdentityComponentSemisimpleOpenNeighbourhood G s :=
  Classical.choice <| by
    obtain ⟨K, hK, aK, hfin, hgal, T, i, hT, hmax⟩ :=
      exists_finiteGalois_hasSplitMaximalTorus torusFiniteGaloisSplitting
        maximalTorusBaseChange ((baseChange (S.fromSpecResidueField s)).obj G)
    let : Field K := hK
    let : Algebra (S.residueField s) K := aK
    let : FiniteDimensional (S.residueField s) K := hfin
    let : IsGalois (S.residueField s) K := hgal
    let d := Langlands.AlgebraicGeometry.etaleResidueExtension S s K
    let : Etale d.projection := d.etale
    let q := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))
    let ε := baseChangeCompIso (S.fromSpecResidueField s) q G
    let j : T.toGrp ⟶ (baseChange d.extensionPoint).obj G := i ≫ ε.inv
    have hm : IsMaximalTorus (T := T) j := hmax.comp_iso ε.symm
    let TC := (CommGroupScheme.baseChange d.inverseResiduePoint).obj T
    let jC := d.torusFibreInclusion G T.toGrp j
    have hTC : IsSplitTorus TC.toGrp := d.torusFibre_isSplit T.toGrp hT
    have hmC : IsMaximalTorus (T := TC) jC :=
      d.torusFibreInclusion_isMaximal G T j hm
    have hsU : d.point ∈ identityComponentSemisimpleLocus ((baseChange d.projection).obj G) := by
      rw [identityComponentSemisimpleLocus_baseChange]
      change d.projection d.point ∈ identityComponentSemisimpleLocus G
      rwa [d.point_over]
    let good := identityComponentSemisimpleNeighbourhood_of_splitMaximalResidueTorus_intrinsic hAffine
      hLift ((baseChange d.projection).obj G)
      d.point hsU TC hTC jC hmC
    have result := identityComponentSemisimpleOpenNeighbourhood_of_openMap G
      d.projection d.projection.isOpenMap d.point good.neighbourhood.isOpen
      good.mem_neighbourhood good.subset_locus
    exact ⟨by simpa only [d.point_over] using result⟩

/-- Actual pointwise good opens give the exact arbitrary-base openness
conclusion from the affine neighbourhood and relative torus-lifting inputs. -/
theorem identityComponentSemisimpleLocusOpen_of_lifting
    (hAffine : IdentityComponentSemisimpleAffineNeighbourhoodStatement.{u})
    (hLift : RelativeSplitTorusLiftingStatement.{u}) :
    IdentityComponentSemisimpleLocusOpenStatement.{u} := by
  intro S G _ _
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  let good := identityComponentSemisimpleNeighbourhood_of_lifting hAffine
    hLift G s hs
  exact ⟨good.neighbourhood, good.subset_locus,
    good.neighbourhood.isOpen, good.mem_neighbourhood⟩

end Langlands.GroupScheme
