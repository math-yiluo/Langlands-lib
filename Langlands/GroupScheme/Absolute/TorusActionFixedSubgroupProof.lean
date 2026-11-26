import Langlands.AlgebraicGeometry.AffineSmoothRetract
import Langlands.GroupScheme.Absolute.TorusActionFixedSubgroupStatement
import Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalProof
import Langlands.GroupScheme.AutomorphicAction.SemidirectComplement
import Langlands.GroupScheme.AutomorphicAction.SemidirectSubgroup
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.RepresentedActionFixed
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedReduction

/-! # Fixed subgroups of torus actions on smooth connected affine groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open AutomorphicAction

section Centralizer

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G C : GroupScheme B}
    (a : AutomorphicAction S.toGrp G)

private theorem fixedSubgroup_eq_centralizer_comap :
    a.fixedSubgroup = (torusCentralizer a.semidirectInr).comap a.semidirectInl := by
  rw [← conjugation_fixedSubgroup_eq_torusCentralizer]
  exact fixedSubgroup_eq_comap_of_equivariant_mono (conjugation a.semidirectInr) a
    a.semidirectInl (fun _ s g => (a.semidirect_conjugation s g).symm)

private theorem mem_semidirectCentralizer_iff {T : Over B} (z : T ⟶ a.semidirectProduct.X) :
    z ∈ (torusCentralizer a.semidirectInr).carrier T ↔
      (a.semidirectPointsEquiv T z).left ∈ a.fixedSubgroup.carrier T := by
  let s := (a.semidirectPointsEquiv T z).right
  have hs : s ≫ a.semidirectInr.hom.hom ∈ (torusCentralizer a.semidirectInr).carrier T := by
    rw [mem_torusCentralizer]
    intro V f t
    change (f ≫ s ≫ a.semidirectInr.hom.hom) * (t ≫ a.semidirectInr.hom.hom) =
      (t ≫ a.semidirectInr.hom.hom) * (f ≫ s ≫ a.semidirectInr.hom.hom)
    simp only [← Category.assoc, ← MonObj.mul_comp, mul_comm (f ≫ s) t]
  rw [fixedSubgroup_eq_centralizer_comap a, SubgroupFunctor.mem_comap]
  conv_lhs => rw [a.semidirect_point_decomposition z]
  exact ((torusCentralizer a.semidirectInr).carrier T).mul_mem_cancel_right hs

variable (c : C ⟶ G) (hc : a.fixedSubgroup.IsRepresentedBy c)

/-- Include the product of the fixed group and the acting group into the semidirect product. -/
private def fixedCentralizerInclusion :
    (trivial S.toGrp C).semidirectProduct ⟶ a.semidirectProduct :=
  semidirectMap (trivial S.toGrp C) a c (by
    intro T s x
    have hx : x ≫ c.hom.hom ∈ a.fixedSubgroup.carrier T := by
      rw [← hc.2]
      exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    simpa only [trivial_act, Category.id_comp] using
      ((a.mem_fixedSubgroup.mp hx) T (𝟙 T) s).symm)

private theorem fixedCentralizer_isRepresentedBy :
    (torusCentralizer a.semidirectInr).IsRepresentedBy (fixedCentralizerInclusion a c hc) := by
  let : Mono c.hom.hom := hc.1
  refine ⟨semidirectMap_mono a (trivial S.toGrp C) c _, ?_⟩
  ext T z
  dsimp only [fixedCentralizerInclusion]
  rw [mem_range_semidirectMap_iff, hc.2, mem_semidirectCentralizer_iff a]

private theorem fixedCentralizer_isClosedSubgroup (hcc : IsClosedSubgroup c) :
    IsClosedSubgroup (fixedCentralizerInclusion a c hc) :=
  isClosedSubgroup_semidirectMap a (trivial S.toGrp C) c _ hcc

private theorem fixedCentralizerInl_comp :
    (trivial S.toGrp C).semidirectInl ≫ fixedCentralizerInclusion a c hc =
      c ≫ a.semidirectInl := by
  apply hom_ext_points
  intro T x
  apply (a.semidirectPointsEquiv T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc, fixedCentralizerInclusion,
    semidirectMap_points, semidirectInl_points]
  rfl

end Centralizer

section Field

variable {k : Type u} [Field k]
    {S G C : GroupScheme (Spec (CommRingCat.of k))}

private theorem connectedSpace_semidirect (a : AutomorphicAction S G) (hS : IsTorus S)
    [ConnectedSpace G.X.left] : ConnectedSpace a.semidirectProduct.X.left := by
  let : IsAffineHom S.X.hom := hS.isMultiplicativeType.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  let : ConnectedSpace S.X.left := hS.connectedSpace
  let : GeometricallyConnected S.X.hom := S.geometricallyConnected_of_connected
  change ConnectedSpace ↥(pullback G.X.hom S.X.hom)
  infer_instance

private theorem fixedSubgroup_smooth_connected [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hS : IsTorus S)
    (a : AutomorphicAction S G) (c : C ⟶ G) (hc : a.fixedSubgroup.IsRepresentedBy c)
    (hcc : IsClosedSubgroup c) : Smooth C.X.hom ∧ ConnectedSpace C.X.left := by
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { S with comm := hS.isCommMonObj }
  let : IsAffineHom S.X.hom := hS.isMultiplicativeType.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  let : IsAffineHom C.X.hom := hcc.isAffineHom
  let : ConnectedSpace a.semidirectProduct.X.left := connectedSpace_semidirect a hS
  let b := trivial S C
  let j := fixedCentralizerInclusion (S := T) a c hc
  have hj := fixedCentralizer_isRepresentedBy (S := T) a c hc
  have hjc := fixedCentralizer_isClosedSubgroup (S := T) a c hc hcc
  let : Smooth b.semidirectProduct.X.hom :=
    torusCentralizerSmooth k a.semidirectProduct T a.semidirectInr hS
      a.isClosedSubgroup_semidirectInr b.semidirectProduct j hj hjc
  let : ConnectedSpace b.semidirectProduct.X.left :=
    IsTorus.connectedSpace_centralizer (T := T) hS a.semidirectInr hj
  let r : b.semidirectProduct.X ⟶ C.X := fst C.X S.X
  have hret : b.semidirectInl.hom.hom ≫ r = 𝟙 C.X := by
    rw [b.semidirectInl_hom]
    exact lift_fst _ _
  refine ⟨AffineRetractGeometry.SchemeRetract.smooth ⟨_, r, hret⟩, ?_⟩
  have hr : Function.Surjective r.left := by
    intro x
    refine ⟨b.semidirectInl.hom.hom.left x, ?_⟩
    simpa [Over.comp_left, Over.id_left, Scheme.Hom.comp_apply]
      using congrArg (fun f : C.X ⟶ C.X => f.left x) hret
  exact hr.connectedSpace r.left.continuous

variable [IsAlgClosed k]

/-- A smooth connected normal factor has the same unipotent radical after adjoining a torus. -/
private theorem radical_semidirectInl [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (a : AutomorphicAction S G) (hS : IsSplitTorus S)
    {U : GroupScheme (Spec (CommRingCat.of k))} (u : U ⟶ G) (hu : IsUnipotentRadical u) :
    IsUnipotentRadical (u ≫ a.semidirectInl) := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  have hi := a.isClosedSubgroup_semidirectInl
  have hin : (SubgroupFunctor.range a.semidirectInl).IsNormal := by
    rw [a.range_semidirectInl]
    apply SubgroupFunctor.IsNormal.comap
    intro T g x _ hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  refine ⟨hu.isClosedSubgroup.comp hi, hu.smooth, hu.connectedSpace, hu.isUnipotent,
    hu.isNormal_comp a.semidirectInl hi hin, ?_⟩
  intro W w hw hws hwc hwu hwn
  let : IsClosedImmersion w.hom.hom.left := hw
  let : Mono w.hom.hom := Over.mono_of_mono_left _
  let f := a.semidirectNormalSubgroup w hwu hS
  have hf : f ≫ a.semidirectInl = w := a.semidirectNormalSubgroup_comp w hwu hS
  have hle := hu.greatest W f (IsClosedSubgroup.of_comp hi (hf ▸ hw)) hws hwc hwu
    (a.semidirectNormalFactor_isNormal w f hf hwn)
  rw [← hf]
  exact SubgroupFunctor.range_comp_mono hle a.semidirectInl

private theorem fixedSubgroup_radical [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [Smooth C.X.hom] [ConnectedSpace C.X.left]
    (hS : IsTorus S) (a : AutomorphicAction S G) (c : C ⟶ G)
    (hc : a.fixedSubgroup.IsRepresentedBy c) (hcc : IsClosedSubgroup c)
    {U V : GroupScheme (Spec (CommRingCat.of k))} (u : U ⟶ G) (hu : IsUnipotentRadical u)
    (v : V ⟶ C) (hv : IsUnipotentRadical v) :
    SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ a.fixedSubgroup := by
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { S with comm := hS.isCommMonObj }
  let : IsAffineHom S.X.hom := hS.isMultiplicativeType.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  let : IsAffineHom C.X.hom := hcc.isAffineHom
  let : ConnectedSpace a.semidirectProduct.X.left := connectedSpace_semidirect a hS
  let b := trivial S C
  let j := fixedCentralizerInclusion (S := T) a c hc
  have hj := fixedCentralizer_isRepresentedBy (S := T) a c hc
  have hjc := fixedCentralizer_isClosedSubgroup (S := T) a c hc hcc
  have hs : IsSplitTorus S := hS.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have h := torusCentralizerUnipotentRadical k a.semidirectProduct T a.semidirectInr
    hS a.isClosedSubgroup_semidirectInr b.semidirectProduct j hj hjc
    U (u ≫ a.semidirectInl) (radical_semidirectInl a hs u hu)
    V (v ≫ b.semidirectInl) (radical_semidirectInl b hs v hv)
  rw [Category.assoc v, fixedCentralizerInl_comp (S := T) a c hc,
    ← Category.assoc v c a.semidirectInl] at h
  have h' := congrArg (fun F : SubgroupFunctor a.semidirectProduct => F.comap a.semidirectInl) h
  rw [range_comp_comap_of_mono, SubgroupFunctor.comap_inf, range_comp_comap_of_mono, hj.2,
    ← fixedSubgroup_eq_centralizer_comap (S := T) a] at h'
  exact h'

end Field

/-- A closed representative of the fixed subgroup of a torus acting on a smooth connected
affine group is smooth and connected and inherits reductivity. Over an algebraically
closed field its unipotent radical is the fixed part of the ambient radical on all tests. -/
theorem torusActionFixedSubgroup : TorusActionFixedSubgroupStatement.{u} := by
  intro k _ G _ _ _ S hS a C c hc hcc
  obtain ⟨hsm, hconn⟩ := fixedSubgroup_smooth_connected hS a c hc hcc
  let : Smooth C.X.hom := hsm
  let : ConnectedSpace C.X.left := hconn
  let : IsAffineHom C.X.hom := hcc.isAffineHom
  refine ⟨⟨hsm, hconn⟩, ?_, ?_⟩
  · intro hG
    refine ⟨hsm, inferInstance, hconn, ?_⟩
    let b := toAlgebraicClosure k
    let F := GroupScheme.baseChange b
    let Gbar := F.obj G
    let Cbar := F.obj C
    have hcbar : (a.baseChange b).fixedSubgroup.IsRepresentedBy (F.map c) := by
      rw [fixedSubgroup_baseChange]
      exact hc.baseChange b
    let : Mono (F.map c).hom.hom := hcbar.1
    let : Smooth Gbar.X.hom := by
      change Smooth (pullback.snd G.X.hom b)
      infer_instance
    let : IsAffineHom Gbar.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom b)
      infer_instance
    let : ConnectedSpace Gbar.X.left := hG.connectedSpace_toAlgebraicClosure
    let : Smooth Cbar.X.hom := by
      change Smooth (pullback.snd C.X.hom b)
      infer_instance
    let : IsAffineHom Cbar.X.hom := (hcc.baseChange b).isAffineHom
    let : ConnectedSpace Cbar.X.left := C.connectedSpace_baseChange_of_smooth_affine b
    obtain ⟨_, u, hu⟩ := unipotentRadicalExistence (AlgebraicClosure k) Gbar
    obtain ⟨_, v, hv⟩ := unipotentRadicalExistence (AlgebraicClosure k) Cbar
    have hr := fixedSubgroup_radical (hS.baseChange (K := AlgebraicClosure k))
      (a.baseChange b) (F.map c) hcbar (hcc.baseChange b) u hu v hv
    apply hv.hasTrivialUnipotentRadical_iff.mpr
    apply (SubgroupFunctor.range_comp_eq_bot_iff v (F.map c)).mp
    rw [hr, hu.range_eq_bot hG.hasTrivialGeometricUnipotentRadical]
    apply SubgroupFunctor.ext
    intro T
    simp only [SubgroupFunctor.inf_carrier, SubgroupFunctor.bot_carrier, bot_inf_eq]
  · intro _ U u hu V v hv
    exact fixedSubgroup_radical hS a c hc hcc u hu v hv

end Langlands.GroupScheme
