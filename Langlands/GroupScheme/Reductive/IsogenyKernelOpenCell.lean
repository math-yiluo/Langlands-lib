import Langlands.GroupScheme.Torus.FiniteHomCentralizer
import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.SubgroupFunctor.KernelCell

/-! # Finite kernels inside open cells containing a self-centralizing torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, the full finite kernel lands in any
open cell containing a self-centralizing torus. No reducedness of the kernel is used. -/
theorem range_kernelι_subset_openCell_algClosed [IsAlgClosed k]
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    (a : T.X ⟶ C) (ha : a ≫ c = i.hom.hom) :
    Set.range (kernelι q).hom.hom.left ⊆ Set.range c.left := by
  have : IsFinite (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  have : IsLocallyArtinian (kernel q).X.left :=
    .of_locallyQuasiFinite (kernel q).X.hom
  rintro _ ⟨x, rfl⟩
  let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (kernel q).X :=
    Over.homMk (pointOfClosedPoint (kernel q).X.hom x (isClosed_singleton))
      (pointOfClosedPoint_comp _ _ _)
  let g := p ≫ (kernelι q).hom.hom
  have hg : g ≫ q.hom.hom = 1 := (kernelPointsEquiv q _ p).property
  have hc : g ∈ (torusCentralizer i).carrier _ := by
    apply mem_torusCentralizer_of_finiteHom q hT i g
    rw [hg]
    exact one_mem _
  rw [hself] at hc
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hc
  refine ⟨(t ≫ a).left (IsLocalRing.closedPoint k), ?_⟩
  have he := congrArg (fun f => f.left (IsLocalRing.closedPoint k))
    ((Category.assoc t a c).trans ((congrArg (t ≫ ·) ha).trans ht))
  have hp : p.left (IsLocalRing.closedPoint k) = x :=
    pointOfClosedPoint_apply _ _ _ _
  simpa only [g, Over.comp_left, Scheme.Hom.comp_apply, hp] using he

/-- Over an arbitrary field, the full finite kernel lands in an open cell
containing a self-centralizing torus. -/
theorem range_kernelι_subset_openCell
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left]
    (a : T.X ⟶ C) (ha : a ≫ c = i.hom.hom) :
    Set.range (kernelι q).hom.hom.left ⊆ Set.range c.left := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  let cK := (Over.pullback b).map c
  have : IsFinite (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) b q.hom.hom inferInstance
  have : IsOpenImmersion cK.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b c inferInstance
  have hselfK : torusCentralizer
      (T := (CommGroupScheme.baseChange b).obj T) (B.map i) =
      SubgroupFunctor.range (B.map i) := by
    rw [torusCentralizer_baseChange, SubgroupFunctor.range_baseChangeHom, hself]
  have hK := range_kernelι_subset_openCell_algClosed
    (T := (CommGroupScheme.baseChange b).obj T)
    (B.map q) (hT.baseChange (K := AlgebraicClosure k)) (B.map i) hselfK
    cK ((Over.pullback b).map a) (by
      rw [← (Over.pullback b).map_comp, ha]
      rfl)
  let w := FiniteEtaleImage.liftOver cK (kernelι (B.map q)).hom.hom hK
  let w' : (B.obj (kernel q)).X ⟶ (Over.pullback b).obj C :=
    (kernelBaseChangeIso b q).hom.hom.hom ≫ w
  have hw : w' ≫ cK = (Over.pullback b).map (kernelι q).hom.hom := by
    dsimp only [w', w]
    rw [Category.assoc, FiniteEtaleImage.liftOver_fac]
    exact congrArg (fun z => z.hom.hom) (kernelBaseChangeIso_hom_ι b q)
  let V := (Over.map b).obj (B.obj (kernel q)).X
  let p : V ⟶ (kernel q).X :=
    ((Over.mapPullbackAdj b).homEquiv (B.obj (kernel q)).X (kernel q).X).symm (𝟙 _)
  let v : V ⟶ C :=
    ((Over.mapPullbackAdj b).homEquiv (B.obj (kernel q)).X C).symm w'
  have : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  have : Surjective p.left := by
    change Surjective (pullback.fst (kernel q).X.hom b)
    infer_instance
  apply FiniteEtaleImage.range_subset_of_surjective_factor c
    (kernelι q).hom.hom p v
  have he := congrArg
    (((Over.mapPullbackAdj b).homEquiv (B.obj (kernel q)).X G.X).symm) hw
  rw [(Over.mapPullbackAdj b).homEquiv_naturality_right_symm w' c] at he
  have hp := (Over.mapPullbackAdj b).homEquiv_naturality_right_symm
    (𝟙 (B.obj (kernel q)).X) (kernelι q).hom.hom
  exact he.trans (by
    simpa only [Category.id_comp] using hp)

/-- The actual factorization of the full kernel through an open cell. -/
def kernelOpenCellLift
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left]
    (a : T.X ⟶ C) (ha : a ≫ c = i.hom.hom) :
    (kernel q).X ⟶ C :=
  FiniteEtaleImage.liftOver c (kernelι q).hom.hom
    (range_kernelι_subset_openCell q hT i hself c a ha)

@[reassoc (attr := simp)]
theorem kernelOpenCellLift_fac
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left]
    (a : T.X ⟶ C) (ha : a ≫ c = i.hom.hom) :
    kernelOpenCellLift q hT i hself c a ha ≫ c = (kernelι q).hom.hom :=
  FiniteEtaleImage.liftOver_fac _ _ _

end Langlands.GroupScheme
