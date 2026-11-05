import Langlands.GroupScheme.Rational.PolynomialHomFiniteDescent
import Langlands.GroupScheme.Rational.PolynomialNormImage
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof
import Langlands.GroupScheme.Rational.SplitTorusDominationPower
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Reductive.GroundFieldRadical

/-! # Splitness of commutative unipotent groups in characteristic zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsCommMonObj G.X]

/-- A nontrivial commutative unipotent group in characteristic zero has a
nontrivial smooth connected central split subgroup over the original field. -/
theorem exists_central_split_subgroup_of_commutative_charZero
    (hU : IsUnipotent G) (hne : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
      IsClosedSubgroup i ∧ Smooth N.X.hom ∧ IsAffineHom N.X.hom ∧
      ConnectedSpace N.X.left ∧ IsCentral i ∧ IsSplitUnipotent N ∧
      SubgroupFunctor.range i ≠ ⊥ := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let L := AlgebraicClosure k
  let b := algebraBaseMap k L
  let Gclosure := (GroupScheme.baseChange b).obj G
  have hfaith : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat b := hfaith.1
  let : Surjective b := hfaith.2
  let : QuasiCompact b := by dsimp [b, algebraBaseMap]; infer_instance
  let : Smooth Gclosure.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom Gclosure.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace Gclosure.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  let : IsCommMonObj Gclosure.X :=
    Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  have hneL : SubgroupFunctor.range (𝟙 Gclosure) ≠ ⊥ := by
    intro h
    apply hne
    apply SubgroupFunctor.eq_bot_of_baseChange_eq_bot b
    rw [← SubgroupFunctor.range_baseChangeHom, CategoryTheory.Functor.map_id]
    exact h
  obtain ⟨n, hV⟩ := commutativeUnipotentVectorCharZero L
    ({ toGrp := Gclosure, comm := inferInstance } : CommGroupScheme _)
    inferInstance inferInstance inferInstance hU.baseChange
  have hn : 0 < n := hV.pos_of_range_ne_bot hneL
  let f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ Gclosure := hV.iso.inv
  let : Mono f.hom.hom := by dsimp [f]; infer_instance
  let j : Fin n := ⟨0, hn⟩
  let v : Fin n → k := Pi.single j 1
  have hv : PolynomialPoint.inputTangent k L G f v ≠ 0 :=
    PolynomialPoint.inputTangent_ne_zero k L G f v j (by simp [v])
  let D := PolynomialPoint.finiteGaloisHomModel (k := k) (L := L) (G := G) f
  have hvD : PolynomialPoint.inputTangent k D.field G D.hom v ≠ 0 :=
    D.inputTangent_ne_zero v hv
  let : IsCommMonObj
      ((GroupScheme.baseChange (algebraBaseMap k D.field)).obj G).X :=
    Functor.isCommMonObj_obj (F := Over.pullback (algebraBaseMap k D.field)) (M := G.X)
  have hcentral : IsCentral D.hom := by
    intro T x T' a y
    exact mul_comm _ _
  obtain ⟨a, ha⟩ := PolynomialPoint.exists_normOfCentralHom_tangent_ne_zero
    k D.field G D.hom hcentral v hvD
  let q := PolynomialPoint.normOfCentralHom k D.field G D.hom hcentral a
  have hqcent : IsCentral q :=
    PolynomialPoint.normOfCentralHom_isCentral k D.field G D.hom hcentral a
  have hVbase : IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of k) n) n :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) n, VectorGroup.isNaturalVectorCoordinates⟩
  let := hVbase.isAffineHom
  let := hVbase.smooth
  let := hVbase.connectedSpace
  have hqne : Lie.targetMapLinear q k ≠ 0 := by
    intro hz
    exact ha (LinearMap.congr_fun hz
      (Additive.ofMul (PolynomialPoint.vectorTangent v)))
  let d := PolynomialPoint.centralSplitImageOfNonzeroDifferential
    q hVbase.isSplitUnipotent hqcent hqne
  exact ⟨d.groupScheme, d.inclusion, d.closed, d.smooth, d.affine, d.connected,
    d.central, d.split, d.range_ne_bot⟩

/-- Smooth connected affine commutative unipotent groups in characteristic
zero are split over their original ground field. -/
theorem IsUnipotent.isSplitUnipotent_of_commutative_charZero
    (hU : IsUnipotent G) : IsSplitUnipotent G := by
  classical
  refine smoothConnectedAffineGroup_lieDimension_induction
    (fun H => IsCommMonObj H.X → IsUnipotent H → IsSplitUnipotent H)
    ?_ G inferInstance hU
  intro H _ _ _ ih hcomm hHu
  let : IsCommMonObj H.X := hcomm
  by_cases ht : SubgroupFunctor.range (𝟙 H) = ⊥
  · exact ⟨0, ht⟩
  obtain ⟨N, i, hi, hNs, hNa, hNc, _hc, hNsplit, hne⟩ :=
    exists_central_split_subgroup_of_commutative_charZero H hHu ht
  let : Smooth N.X.hom := hNs
  let : IsAffineHom N.X.hom := hNa
  let : ConnectedSpace N.X.left := hNc
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hnormal : (SubgroupFunctor.range i).IsNormal := by
    intro T g x _ hx
    rw [mul_comm g x, mul_inv_cancel_right]
    exact hx
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k H N i hi hnormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : ConnectedSpace Q.X.left := hq.connectedSpace
  let : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp q.hom.hom.left Q.X.hom
  let : QuasiCompact q.hom.hom.left := inferInstance
  let : IsCommMonObj Q.X := hq.isCommMonObj
  have hlt : Lie.dimension Q < Lie.dimension H :=
    hq.lieDimension_lt_of_nontrivial_connected_kernel
      (n := i) ⟨inferInstance, rfl⟩ hNs hne
  obtain ⟨n, hn⟩ := ih Q hlt inferInstance (hHu.of_flat_surjective q)
  obtain ⟨m, hm⟩ := hNsplit
  exact ⟨m + n, hm.of_fppfQuotient_of_field i q hi inferInstance hq hn⟩

/-- Choose an actual finite represented additive series over the original field. -/
def splitSeriesOfCommutativeCharZero (hU : IsUnipotent G) :
    {n : ℕ // HasSplitSeries n G} :=
  let h := IsUnipotent.isSplitUnipotent_of_commutative_charZero G hU
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme.RelativeRoot
