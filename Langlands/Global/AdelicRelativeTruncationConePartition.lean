import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport
import Langlands.LinearAlgebra.TruncatedObtuseConePartition

/-! # The truncated negative cone partition in the relative coroot space -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.GroupScheme.ArthurRelative Langlands.LinearAlgebra

variable {F : Type*} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)

local notation "Δ" => simpleRelativeRoots i ν
local notation "Vg" => D.realCorootSpan
local notation "w" => weight hG hi ν D Δ

/-- The regions of (7.26) in relative coroot coordinates, with origin translated
by the split projection of the base parameter. The negative Levi member is `-Z`. -/
def IsRelativeTruncatedConeDecomposition (I Q : Global.StandardIndex F G i ν)
    (S X Y Z : Vg) : Prop :=
  I.val ⊆ Q.val ∧ X = Y - Z ∧
    ((Y : V T) ∈ aSpace T Q.val ∧ ∀ α ∈ Δ, 0 ≤ eval T α (Y : V T)) ∧
    (∀ α ∈ Δ \ Q.val, w α ((Y : V T) - (S : V T)) ≤ 0) ∧
    (Z : V T) ∈ aSpace T I.val ∧
    (∀ α ∈ Q.val \ I.val, 0 < w α (Z : V T)) ∧
    (∀ α ∈ Δ \ Q.val, w α (Z : V T) = 0)

/-- A point of the translated relative negative cone has a unique standard Levi
face and a unique decomposition into the split and Levi members. -/
def RelativeTruncationConePartitionStatement : Prop :=
  ∀ {B : LinearMap.BilinForm ℝ (V T)}, IsWeylInvariantCocharacterInnerProduct i B →
  IsGenericCocharacter i ν → ∀ (I : Global.StandardIndex F G i ν) (S : Vg),
  (∀ α ∈ Δ, 0 ≤ eval T α (S : V T)) → ∀ X : Vg,
  ((X : V T) ∈ aSpace T I.val ∧ ∀ α ∈ Δ \ I.val, w α ((X : V T) - (S : V T)) ≤ 0) ↔
    ∃! d : Global.StandardIndex F G i ν × Vg × Vg,
      IsRelativeTruncatedConeDecomposition hG hi D I d.1 S X d.2.1 d.2.2

variable (hν : IsGenericCocharacter i ν)

local notation "b" => RootPairing.Base.toCoweightBasis (base hG hi hν D)
local notation "Ι" => Subtype (fun j => j ∈ RootPairing.Base.support (base hG hi hν D))

private def rootOfIndex (j : Ι) : characterLattice T := j.1.1

private theorem rootOfIndex_mem (j : Ι) : rootOfIndex hG hi D hν j ∈ Δ :=
  (mem_support_base hG hi hν D).mp j.2

private theorem rootOfIndex_injective : Function.Injective (rootOfIndex hG hi D hν) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

private theorem exists_index_of_mem {α : characterLattice T} (hα : α ∈ Δ) :
    ∃ j : Ι, rootOfIndex hG hi D hν j = α :=
  ⟨⟨⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν hα⟩,
     (mem_support_base hG hi hν D).mpr hα⟩, rfl⟩

private def indexSetEquiv : Global.StandardIndex F G i ν ≃ Set Ι where
  toFun J := rootOfIndex hG hi D hν ⁻¹' J.val
  invFun U := ⟨rootOfIndex hG hi D hν '' U, fun _ ⟨j, _, h⟩ => h ▸ rootOfIndex_mem hG hi D hν j⟩
  left_inv J := by
    apply Subtype.ext
    ext α
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hα
      obtain ⟨j, rfl⟩ := exists_index_of_mem hG hi D hν (J.property hα)
      exact ⟨j, hα, rfl⟩
  right_inv U := Set.preimage_image_eq _ (rootOfIndex_injective hG hi D hν)

private theorem weight_eq_corootCoord (j : Ι) (x : Vg) :
    w (rootOfIndex hG hi D hν j) (x : V T) = (b).coord j x := by
  let := finite_indivisibleRoots hG hi
  rw [Module.Basis.coord_apply, ArthurCombinatorics.toCoweightBasis_repr_eq,
    show rootOfIndex hG hi D hν j = (j.1 : characterLattice T) from rfl,
    weight_coe hG hi ν D Δ j.1, standardIndex_simpleRelativeRoots hG hi D hν, toCorootSpan_apply_coe]

include hi in
private theorem pairing_eq_mul_eval {B : LinearMap.BilinForm ℝ (V T)}
    (hB : IsWeylInvariantCocharacterInnerProduct i B) (α : relativeRoots i) (x : V T) :
    B x (D.realCoroot α) = (B (D.realCoroot α) (D.realCoroot α) / 2) * eval T α.1 x := by
  let g : relativeWeylGroup i := QuotientGroup.mk (D.representative α)
  have he (v : V T) : relativeWeylRealAction i g v = v - eval T α.1 v • D.realCoroot α := by
    simpa only [eval_eq_pair] using D.real_coreflection hi.isSplitSubtorus.1 α v
  have hn : relativeWeylRealAction i g (D.realCoroot α) = -D.realCoroot α := by
    rw [he, eval_eq_pair, D.pair_root_realCoroot]
    module
  have h := hB.2.2 g x (D.realCoroot α)
  rw [he x, hn] at h
  simp only [map_sub, map_neg, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
  linarith

private theorem restrictedPairing_eq_mul_eval {B : LinearMap.BilinForm ℝ (V T)}
    (hB : IsWeylInvariantCocharacterInnerProduct i B) (j : Ι) (x : Vg) :
    ∃ c : ℝ, 0 < c ∧ B.restrict Vg x (b j) = c * eval T (rootOfIndex hG hi D hν j) (x : V T) := by
  let α : relativeRoots i := ⟨j.1.1, j.1.2.1⟩
  have hn : D.realCoroot α ≠ 0 := by
    intro h
    have hc := congrArg (eval T α.1) h
    rw [eval_eq_pair, D.pair_root_realCoroot, map_zero] at hc
    norm_num at hc
  refine ⟨B (D.realCoroot α) (D.realCoroot α) / 2, div_pos (hB.2.1 _ hn) (by norm_num), ?_⟩
  rw [RootPairing.Base.toCoweightBasis_apply]
  change B x ((rootPairing hG hi D).coroot j.1 : V T) = _
  rw [rootPairing_coroot]
  exact pairing_eq_mul_eval hi D hB α x

/-- Transfer the finite obtuse-basis partition along the actual simple coroot basis. -/
theorem relativeTruncationConePartition : RelativeTruncationConePartitionStatement (ν := ν) hG hi D := by
  intro B hB hν' I S hS X
  let e := indexSetEquiv hG hi D hν'
  let b' := (base hG hi hν' D).toCoweightBasis
  let B' := B.restrict Vg
  let val := rootOfIndex hG hi D hν'
  let := finite_indivisibleRoots hG hi
  have hval (j : ↥(base hG hi hν' D).support) : val j ∈ Δ := rootOfIndex_mem hG hi D hν' j
  have hex (α : characterLattice T) (hα : α ∈ Δ) : ∃ j, val j = α := exists_index_of_mem hG hi D hν' hα
  have hmem (J : Global.StandardIndex F G i ν) (j : ↥(base hG hi hν' D).support) :
      j ∈ e J ↔ val j ∈ J.val := Iff.rfl
  have hpair (v : Vg) (j : ↥(base hG hi hν' D).support) :
      ∃ c : ℝ, 0 < c ∧ B' v (b' j) = c * eval T (val j) v :=
    restrictedPairing_eq_mul_eval hG hi D hν' hB j v
  have hnonneg (v : Vg) (j : ↥(base hG hi hν' D).support) :
      0 ≤ B' v (b' j) ↔ 0 ≤ eval T (val j) v := by
    obtain ⟨c, hc, h⟩ := hpair v j
    rw [h, mul_nonneg_iff_of_pos_left hc]
  have hz (v : Vg) (j : ↥(base hG hi hν' D).support) :
      B' v (b' j) = 0 ↔ eval T (val j) v = 0 := by
    obtain ⟨c, hc, h⟩ := hpair v j
    rw [h, mul_eq_zero, or_iff_right hc.ne']
  have hweights (v : Vg) (j : ↥(base hG hi hν' D).support) : w (val j) v = b'.coord j v :=
    weight_eq_corootCoord hG hi D hν' j v
  have horth (J : Global.StandardIndex F G i ν) (v : Vg) :
      (v : V T) ∈ aSpace T J.val ↔ basisOrthogonal b' B' (e J) v := by
    rw [mem_rootAnnihilator]
    constructor
    · intro hv j hj
      exact (hz v j).mpr (hv (val j) ((hmem J j).mp hj))
    · intro hv α hα
      obtain ⟨j, rfl⟩ := hex α (J.property hα)
      exact (hz v j).mp (hv j ((hmem J j).mpr hα))
  have hclosed (J : Global.StandardIndex F G i ν) (v : Vg) :
      ((v : V T) ∈ aSpace T J.val ∧ ∀ α ∈ Δ, 0 ≤ eval T α (v : V T)) ↔ basisClosedFace b' B' (e J) v := by
    refine and_congr (horth J v) ⟨fun hv j => (hnonneg v j).mpr (hv _ (hval j)), ?_⟩
    intro hv α hα
    obtain ⟨j, rfl⟩ := hex α hα
    exact (hnonneg v j).mp (hv j)
  have houtside (J : Global.StandardIndex F G i ν) (v : Vg) (P : ℝ → Prop) :
      (∀ α ∈ Δ \ J.val, P (w α (v : V T))) ↔ ∀ j ∉ e J, P (b'.coord j v) := by
    constructor
    · intro hv j hj
      rw [← hweights v j]
      exact hv _ ⟨hval j, fun hm => hj ((hmem J j).mpr hm)⟩
    · intro hv α hα
      obtain ⟨j, rfl⟩ := hex α hα.1
      rw [hweights v j]
      exact hv j (fun hm => hα.2 ((hmem J j).mp hm))
  have hpositive (J Q : Global.StandardIndex F G i ν) (v : Vg) :
      (∀ α ∈ Q.val \ J.val, 0 < w α (v : V T)) ↔ ∀ j ∈ e Q \ e J, 0 < b'.coord j v := by
    constructor
    · intro hv j hj
      rw [← hweights v j]
      exact hv _ ⟨(hmem Q j).mp hj.1, fun hm => hj.2 ((hmem J j).mpr hm)⟩
    · intro hv α hα
      obtain ⟨j, rfl⟩ := hex α (Q.property hα.1)
      rw [hweights v j]
      exact hv j ⟨(hmem Q j).mpr hα.1, fun hm => hα.2 ((hmem J j).mp hm)⟩
  have hsub (Q : Global.StandardIndex F G i ν) : I.val ⊆ Q.val ↔ e I ⊆ e Q := by
    constructor
    · intro h j hj
      exact (hmem Q j).mpr (h ((hmem I j).mp hj))
    · intro h α hα
      obtain ⟨j, rfl⟩ := hex α (I.property hα)
      exact (hmem Q j).mp (h ((hmem I j).mpr hα))
  have hobt (j k : ↥(base hG hi hν' D).support) (hne : j ≠ k) : B' (b' j) (b' k) ≤ 0 := by
    have hjk : val k ≠ val j := fun eq => hne ((rootOfIndex_injective hG hi D hν' eq).symm)
    have hr : eval T (val k) ((b' j : Vg) : V T) ≤ 0 := by
      rw [show b' j = (rootPairing hG hi D).coroot j.1 from RootPairing.Base.toCoweightBasis_apply _ _,
        rootPairing_coroot, eval_eq_pair, D.pair_tmul_realCoroot, one_mul]
      exact_mod_cast D.simple_pairing_nonpos i ν hi.isSplitSubtorus.1 (finite_relativeRoots hG hi) hν'
        ⟨val k, hval k⟩ ⟨val j, hval j⟩
        (fun eq => hjk (congrArg (fun α : simpleRelativeRoots i ν => α.val) eq))
    obtain ⟨c, hc, hh⟩ := hpair (b' j) k
    rw [hh]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hr
  have hBpos (v : Vg) (hv : v ≠ 0) : 0 < B' v v :=
    hB.2.1 v (fun he => hv (Subtype.ext he))
  let coordEquiv := e.prodCongr (Equiv.refl (Vg × Vg))
  have hdecomp (d : Global.StandardIndex F G i ν × Vg × Vg) :
      IsRelativeTruncatedConeDecomposition hG hi D I d.1 S X d.2.1 d.2.2 ↔
        IsTruncatedBasisConeDecomposition b' B' (e I) S X (coordEquiv d).1 (coordEquiv d).2.1 (coordEquiv d).2.2 := by
    rcases d with ⟨Q, Y, Z⟩
    exact and_congr (hsub Q) <| and_congr Iff.rfl <| and_congr (hclosed Q Y) <|
      and_congr (houtside Q (Y - S) (· ≤ 0)) <| and_congr (horth I Z) <|
        and_congr (hpositive I Q Z) (houtside Q Z (· = 0))
  have habstract := truncatedBasisConePartition b' B' (fun x y => hB.1 x y) hBpos hobt (e I) S
    (fun j => (hnonneg S j).mpr (hS _ (hval j))) X
  exact (and_congr (horth I X) (houtside I (X - S) (· ≤ 0))).trans
    (habstract.trans (coordEquiv.existsUnique_congr hdecomp).symm)

end Langlands.Global.ArthurTruncation
