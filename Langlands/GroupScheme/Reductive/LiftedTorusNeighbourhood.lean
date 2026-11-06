import Langlands.GroupScheme.Reductive.TorusFibreMaximality

/-! # Good neighbourhoods from a relative torus maximal at a field point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

namespace Langlands.GroupScheme

local instance lifted_smooth_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance lifted_affine_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Reverse maximality transport through the actual composite pullback. -/
theorem isMaximalTorus_of_baseChange_comp
    {S U : Scheme.{u}} (a : U ⟶ S) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ U) (T : CommGroupScheme S)
    {G : GroupScheme S} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      ((CommGroupScheme.baseChange a).obj T))
      ((baseChange b).map ((baseChange a).map i))) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (b ≫ a)).obj T)
      ((baseChange (b ≫ a)).map i) := by
  have hn := ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i
  change (baseChange (b ≫ a)).map i ≫ (baseChangeCompIso a b G).hom =
    (baseChangeCompIso a b T.toGrp).hom ≫
      (baseChange b).map ((baseChange a).map i) at hn
  have hm := (IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange b).obj ((CommGroupScheme.baseChange a).obj T))
    (T' := (CommGroupScheme.baseChange (b ≫ a)).obj T)
    (baseChangeCompIso a b T.toGrp) hi).comp_iso (baseChangeCompIso a b G).symm
  have he : (baseChangeCompIso a b T.toGrp).hom ≫
      (baseChange b).map ((baseChange a).map i) ≫ (baseChangeCompIso a b G).inv =
      (baseChange (b ≫ a)).map i := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [Iso.symm_hom, Category.assoc, he] using hm

namespace splitTorus

/-- Maximality of the actual standard-torus inclusion is unchanged when its
canonical coordinates are pulled back along a composite field point. -/
theorem isMaximalTorus_baseChangedHom_comp
    {S U : Scheme.{u}} (I : Type u) [Finite I]
    (G : GroupScheme S) (i : splitTorus S I ⟶ G)
    (a : U ⟶ S) {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ U)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (b ≫ a)).obj
      (commGroupScheme S I)) ((baseChange (b ≫ a)).map i)) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj (commGroupScheme U I))
      ((baseChange b).map ((baseChangeIso a I).inv ≫ (baseChange a).map i)) := by
  have hm := isMaximalTorus_baseChange_comp a b (commGroupScheme S I) i hi
  have hs := IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange b).obj
      ((CommGroupScheme.baseChange a).obj (commGroupScheme S I)))
    (T' := (CommGroupScheme.baseChange b).obj (commGroupScheme U I))
    ((baseChange b).mapIso (baseChangeIso a I).symm) hm
  simpa only [Functor.map_comp, Functor.mapIso_hom, Iso.symm_hom] using hs

/-- A maximal torus at a field-valued point stays maximal after composing
that point with an arbitrary field extension. -/
theorem isMaximalTorus_fieldPoint_extension
    {r : Type u} [CommRing r] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hi : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)) :
    IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i
        (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ b)) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hmap : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme _ I)) ((baseChange b).map i) :=
    (IsMaximalTorus.iso_comp_iff (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme _ I)) (T' := commGroupScheme _ I) (baseChangeIso b I).symm _).mp hi
  have hm := (maximalTorusBaseChange k K ((baseChange b).obj G)
    ((CommGroupScheme.baseChange b).obj (commGroupScheme _ I))
    ((baseChange b).map i) hmap.1 hmap.2.1).mp hmap
  have hc := isMaximalTorus_of_baseChange_comp b c (commGroupScheme _ I) i hm
  exact IsMaximalTorus.iso_comp (T := (CommGroupScheme.baseChange (c ≫ b)).obj
    (commGroupScheme _ I)) (T' := commGroupScheme _ I) (baseChangeIso (c ≫ b) I).symm hc

set_option maxHeartbeats 600000 in
/-- The affine good-open constructor extends a supplied maximal field-point
fibre to its algebraic closure before testing actual zero weights. -/
def identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_extension
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme _ I)) ((baseChange b).map i)) :
    IdentityComponentReductiveOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
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
      identityComponentReductiveLocus G := by rwa [hpoint]
  have result := identityComponentReductiveNeighbourhood_of_maximal_fieldPoint I G i
    hCentralizer hReflection hReduced hLine hi d hs' hd
  simpa only [hpoint] using result

set_option maxHeartbeats 600000 in
/-- A closed standard torus over any base gives a good neighbourhood at a
field-valued point where its actual fibre is maximal. The field need not
be algebraically closed. -/
def identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_overScheme
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus S I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme S I)) ((baseChange b).map i)) :
    IdentityComponentReductiveOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
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
  have hsA : c (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus H := by
    rw [identityComponentReductiveLocus_baseChange]
    change a (c (IsLocalRing.closedPoint k)) ∈ identityComponentReductiveLocus G
    rwa [hpoint]
  let good := identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_extension
    hCentralizer hReflection hReduced hLine I H iA hiA c hsA hm
  have result := identityComponentReductiveOpenNeighbourhood_of_openMap G a a.isOpenMap
    (c (IsLocalRing.closedPoint k)) good.neighbourhood.isOpen
    good.mem_neighbourhood good.subset_locus
  simpa only [hpoint] using result

end splitTorus

end Langlands.GroupScheme
