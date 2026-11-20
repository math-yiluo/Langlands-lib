import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension
import Langlands.AlgebraicGeometry.PointTopology.RealOpenZariskiDensity
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Cartan.ConjugacyDensityProof
import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.TorusUnirationalityProof

/-! # Density of points in real maximal tori -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- A point that belongs to a maximal torus geometrically belongs to one over the
original field in characteristic zero. -/
theorem exists_maximalTorus_point_of_geometric {k : Type} [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (x : RationalPoint k G.X)
    (h : ∃ (T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (j : T.toGrp ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G),
      IsMaximalTorus j ∧ ∃ t : RationalPoint (AlgebraicClosure k) T.X,
        t ≫ j.hom.hom = geometricRationalPoint (K := AlgebraicClosure k) G.X x) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j ∧ ∃ t : RationalPoint k T.X, t ≫ j.hom.hom = x := by
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let bc := GroupScheme.baseChange b
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨C, i, hi, hclosed⟩ := G.pointCentralizer_isClosedRepresentable x
  let : IsClosedImmersion i.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := hclosed.isAffineHom
  let : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth C.X.hom := affineCartierSmooth k C inferInstance inferInstance
  let C₀ := identityComponent C
  let c : C₀ ⟶ G := identityComponentι C ≫ i
  have hcl : IsClosedSubgroup c := (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hclosed
  have hfull : ∃ (T : CommGroupScheme (Spec (CommRingCat.of K)))
      (f : T.toGrp ⟶ bc.obj C₀), IsMaximalTorus (f ≫ bc.map c) := by
    obtain ⟨T, j, hj, t, ht⟩ := h
    let xK : RationalPoint K (bc.obj G).X := geometricRationalPoint (K := K) G.X x
    have hxK : (baseChangeBasePointsEquiv b G).symm (toUnit (Over.mk b) ≫ x) = xK := by
      rw [show toUnit (Over.mk b) = Over.homMk b (by simp) from toUnit_unique _ _]
      change baseChangeSectionHom b G x = xK
      apply Over.OverMorphism.ext
      rw [baseChangeSectionHom_left]
      rfl
    have hiK := hi.baseChange b
    rw [pointCentralizer_baseChange, hxK] at hiK
    have hT : SubgroupFunctor.range j ≤ (bc.obj G).pointCentralizer xK := by
      intro Z z hz
      obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hz
      have ht' : t ≫ j.hom.hom = xK := ht
      have hx' : toUnit Z ≫ xK = (toUnit Z ≫ t) ≫ j.hom.hom := by
        rw [← ht', Category.assoc]
      rw [mem_pointCentralizer, hx', ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
    let f := hiK.factorHom j hT
    have hf : f ≫ bc.map i = j := hiK.factorHom_comp j hT
    let : ConnectedSpace T.X.left := hj.1.connectedSpace
    let Ciso := IdentityComponent.baseChangeIso C (algebraMap k K)
    let f₀ := IdentityComponent.factor (bc.obj C) f ≫ Ciso.inv
    refine ⟨T, f₀, ?_⟩
    have hfac : f₀ ≫ bc.map c = j := by
      rw [show bc.map c = bc.map (identityComponentι C) ≫ bc.map i from bc.map_comp _ _]
      dsimp only [f₀]
      rw [Category.assoc, ← Category.assoc Ciso.inv, IdentityComponent.baseChangeIso_inv_comp,
        IdentityComponent.factor_identityComponentι_assoc]
      exact hf
    exact hfac.symm ▸ hj
  let : ConnectedSpace (bc.obj C₀).X.left := inferInstance
  obtain ⟨T, j, hj⟩ := exists_isMaximalTorus_comp_of_geometric
    maximalTorusExistence maximalTorusBaseChange maximalTorusConjugacy k C₀ G c hcl inferInstance hfull
  refine ⟨T, j ≫ c, hj, SubgroupFunctor.mem_range.mp ?_⟩
  rw [← maximalTorusCentralizer k G hG T (j ≫ c) hj, mem_torusCentralizer]
  intro V a t
  have ha : a = toUnit V := toUnit_unique _ _
  rw [ha]
  have ht : t ≫ (j ≫ c).hom.hom ∈ (SubgroupFunctor.range i).carrier V := by
    refine SubgroupFunctor.mem_range.mpr ⟨t ≫ (j ≫ identityComponentι C).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc]
  rw [hi.2, mem_pointCentralizer] at ht
  exact ht.symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_open_toral_points {k : Type} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    ∃ U : Set G.X.left, IsOpen U ∧ U.Nonempty ∧
      ∀ x : RationalPoint k G.X, x.left (IsLocalRing.closedPoint k) ∈ U →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j ∧ ∃ t : RationalPoint k T.X, t ≫ j.hom.hom = x := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨T, j, hj⟩ := maximalTorusExistence k G
  let F := BorelPointContainment.conjugation j
  obtain ⟨U, hU, hd, hsub⟩ := CartanConjugacyDensity.exists_isOpen_dense_subset_range_conjugation
    (hj.isCartanSubgroup_of_centralizerStatement maximalTorusCentralizer hG)
  refine ⟨U, hU, hd.nonempty, fun x hx => ?_⟩
  let : Smooth T.X.hom := hj.1.smooth
  let : Smooth (G.X ⊗ T.X).hom := smooth_tensor _ _ inferInstance inferInstance
  let : LocallyOfFiniteType (F.left ≫ G.X.hom) := by
    rw [Over.w F]
    infer_instance
  let : LocallyOfFiniteType F.left := locallyOfFiniteType_of_comp F.left G.X.hom
  obtain ⟨z, hz⟩ := exists_rationalPoint_lift_of_mem_range F.left x.left (hsub hx)
  let w : RationalPoint k (G.X ⊗ T.X) := Over.homMk z (by
    rw [← Over.w F, ← Category.assoc, hz]
    exact Over.w x)
  have hw : w ≫ F = x := Over.OverMorphism.ext hz
  let g : RationalPoint k G.X := w ≫ fst G.X T.X
  let t : RationalPoint k T.X := w ≫ snd G.X T.X
  have hw' : w = lift g t := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (lift_fst _ _).symm
    · exact (lift_snd _ _).symm
  refine ⟨T, j ≫ (G.innerIso g).hom, hj.comp_iso _, t, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
  rw [hw', BorelPointContainment.lift_conjugation] at hw
  exact hw

/-- Real points lying in a real maximal torus are dense in a connected reductive group. -/
def RealToralPointsDenseStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    IsConnectedReductive G → Dense { p : RingPoint ℝ G.X ℝ |
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (j : T.toGrp ⟶ G),
        IsMaximalTorus j ∧ ∃ t : RingPoint ℝ T.X ℝ, t ≫ j.hom.hom = p }

set_option backward.isDefEq.respectTransparency false in
theorem realToralPointsDense : RealToralPointsDenseStatement := by
  intro G _ hG
  let K := AlgebraicClosure ℝ
  let b := toAlgebraicClosure ℝ
  let Gbar := (GroupScheme.baseChange b).obj G
  have hGbar : IsConnectedReductive Gbar :=
    connectedReductiveFieldExtensionStatement ℝ K G hG
  obtain ⟨U, hU, hUne, htoral⟩ := exists_open_toral_points Gbar hGbar
  have huni := ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality G hG
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  let π := pullback.fst G.X.hom b
  have hD := (realOpenZariskiDensity G huni W hW hWne).preimage π.isOpenMap
  obtain ⟨y, hyU, hyW⟩ := hD.inter_open_nonempty U hU hUne
  change π y ∈ underlyingRealPoint G.X '' W at hyW
  obtain ⟨p, hp, hpy⟩ := hyW
  let x : RationalPoint ℝ G.X := (rationalPointEquiv ℝ G.X).symm p
  have hx : x.left (IsLocalRing.closedPoint ℝ) = π y := by
    rw [show x.left = p.left from rationalPointEquiv_symm_left ℝ G.X p]
    exact hpy
  let xbar : RationalPoint K Gbar.X := geometricRationalPoint (K := K) G.X x
  have hyb : y ∈ Set.range xbar.left := by
    change y ∈ Set.range (geometricRationalPoint (K := K) G.X x).left
    rw [range_geometricRationalPoint]
    exact ⟨IsLocalRing.closedPoint ℝ, hx⟩
  obtain ⟨a, ha⟩ := hyb
  have ha' : a = IsLocalRing.closedPoint K :=
    @Subsingleton.elim (PrimeSpectrum K) inferInstance _ _
  have hxbar : xbar.left (IsLocalRing.closedPoint K) ∈ U := by
    rwa [← ha', ha]
  obtain ⟨T, j, hj, t, ht⟩ := exists_maximalTorus_point_of_geometric G hG x
    (htoral xbar hxbar)
  refine ⟨p, hp, T, j, hj, rationalPointEquiv ℝ T.X t, ?_⟩
  rw [← rationalPointEquiv_natural, ht]
  exact (rationalPointEquiv ℝ G.X).apply_symm_apply p

end Langlands.GroupScheme
