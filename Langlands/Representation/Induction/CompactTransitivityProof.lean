import Langlands.Representation.Induction.CompactTransitivityStatement
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientTopology

/-! Compact induction in stages, with both actual support conditions proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

open QuotientIntegration

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable (H P : Subgroup G) (hHP : H ≤ P)
variable (σ : Representation R H V)

local notation "HP" => H.subgroupOf P
local notation "φ" => (MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP))
local notation "σP" => σ.comp φ
local notation "ρP" => compactInduced HP σP

private theorem compact_ext (f g : CompactFunctions H σ)
    (he : ∀ x, eval H σ f.val x = eval H σ g.val x) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact funext he

private def stageInnerSmooth (f : CompactFunctions H σ) (x : G) :
    SmoothFunctions HP σP := by
  let K := f.val.property.choose
  have hK := f.val.property.choose_spec
  refine smoothFunctionOf HP σP (fun p => eval H σ f.val ((p : G) * x))
    (fun h p => ?_) (conjOpenSubgroup P K x) (fun k p => ?_)
  · change eval H σ f.val (((h : P) : G) * (p : G) * x) =
      σ (φ h) (eval H σ f.val ((p : G) * x))
    have hh : ((φ h : H) : G) = ((h : P) : G) := rfl
    simpa only [mul_assoc, hh] using
      eval_covariant H σ f.val (φ h) ((p : G) * x)
  · have hk : x⁻¹ * ((k : P) : G) * x ∈ K := mem_conjOpenSubgroup.mp k.property
    have he := congrArg (fun F : EquivariantFunctions H σ => F.val ((p : G) * x))
      (hK ⟨_, hk⟩)
    change eval H σ f.val (((p : G) * x) * (x⁻¹ * ((k : P) : G) * x)) =
      eval H σ f.val ((p : G) * x) at he
    change eval H σ f.val ((((p : P) : G) * ((k : P) : G)) * x) =
      eval H σ f.val ((p : G) * x)
    simpa only [eval, mul_assoc, mul_inv_cancel_left] using he

@[simp] private theorem stageInnerSmooth_eval (f : CompactFunctions H σ) (x : G) (p : P) :
    eval HP σP (stageInnerSmooth H P hHP σ f x) p =
      eval H σ f.val ((p : G) * x) := rfl

section Compact

variable [LocallyCompactSpace G]
variable (hH : IsClosed (H : Set G)) (hP : IsClosed (P : Set G))

include hH hP

private theorem stageInner_compact (f : CompactFunctions H σ) (x : G) :
    IsCompact (quotientSupport HP (eval HP σP (stageInnerSmooth H P hHP σ f x))) := by
  obtain ⟨C, hCc, hCq⟩ := leftQuotient_exists_isCompact_image H hH f.property
  let D : Set P := P.subtype ⁻¹' ((fun c : G => c * x⁻¹) '' C)
  have hDc : IsCompact D := hP.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hCc.image (continuous_id.mul_const x⁻¹))
  apply (hDc.image (leftQuotient_isOpenQuotientMap HP).continuous).of_isClosed_subset
    (isClosed_quotientSupport HP σP (stageInnerSmooth H P hHP σ f x))
  rintro _ ⟨p, hp, rfl⟩
  have hp' : eval H σ f.val ((p : G) * x) ≠ 0 := by
    simpa only [Function.mem_support, stageInnerSmooth_eval] using hp
  have hpx : quotientMap H ((p : G) * x) ∈ quotientSupport H (eval H σ f.val) :=
    ⟨_, hp', rfl⟩
  rw [← hCq] at hpx
  obtain ⟨c, hc, hcx⟩ := hpx
  have hh : (p : G) * x * c⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcx)
  have hcP : c * x⁻¹ ∈ P := by
    have hm := P.mul_mem (P.inv_mem (hHP hh)) p.property
    simpa [mul_assoc] using hm
  let d : P := ⟨c * x⁻¹, hcP⟩
  refine ⟨d, ⟨c, hc, rfl⟩, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel HP d p
  rw [QuotientGroup.rightRel_apply]
  change (p : G) * (c * x⁻¹)⁻¹ ∈ H
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh

private def stageInner (f : CompactFunctions H σ) (x : G) : CompactFunctions HP σP :=
  ⟨stageInnerSmooth H P hHP σ f x, stageInner_compact H P hHP σ hH hP f x⟩

@[simp] private theorem stageInner_eval (f : CompactFunctions H σ) (x : G) (p : P) :
    eval HP σP (stageInner H P hHP σ hH hP f x).val p =
      eval H σ f.val ((p : G) * x) :=
  stageInnerSmooth_eval H P hHP σ f x p

private def stageExpandSmooth (f : CompactFunctions H σ) :
    SmoothFunctions P ρP := by
  let K := f.val.property.choose
  have hK := f.val.property.choose_spec
  refine smoothFunctionOf P ρP (stageInner H P hHP σ hH hP f)
    (fun p x => ?_) K (fun k x => ?_)
  · apply compact_ext
    intro q
    change eval HP σP (stageInner H P hHP σ hH hP f ((p : G) * x)).val q =
      eval HP σP (stageInner H P hHP σ hH hP f x).val (q * p)
    simp only [stageInner_eval, Subgroup.coe_mul, mul_assoc]
  · apply compact_ext
    intro p
    simp only [stageInner_eval]
    have he := congrArg (fun F : EquivariantFunctions H σ => F.val ((p : G) * x)) (hK k)
    change eval H σ f.val (((p : G) * x) * (k : G)) =
      eval H σ f.val ((p : G) * x) at he
    simpa only [mul_assoc] using he

@[simp] private theorem stageExpandSmooth_eval (f : CompactFunctions H σ) (x : G) :
    eval P ρP (stageExpandSmooth H P hHP σ hH hP f) x =
      stageInner H P hHP σ hH hP f x := rfl

private theorem stageExpand_compact (f : CompactFunctions H σ) :
    IsCompact (quotientSupport P
      (eval P ρP (stageExpandSmooth H P hHP σ hH hP f))) := by
  obtain ⟨C, hCc, hCq⟩ := leftQuotient_exists_isCompact_image H hH f.property
  apply (hCc.image (leftQuotient_isOpenQuotientMap P).continuous).of_isClosed_subset
    (isClosed_quotientSupport P ρP (stageExpandSmooth H P hHP σ hH hP f))
  rintro _ ⟨x, hx, rfl⟩
  have hx' : stageInner H P hHP σ hH hP f x ≠ 0 := by
    simpa only [Function.mem_support, stageExpandSmooth_eval] using hx
  obtain ⟨p, hp⟩ : ∃ p : P, eval H σ f.val ((p : G) * x) ≠ 0 := by
    by_contra hn
    apply hx'
    apply compact_ext
    intro p
    change eval H σ f.val ((p : G) * x) = 0
    exact
      (show ∀ p : P, eval H σ f.val ((p : G) * x) = 0 from by simpa using hn) p
  have hpx : quotientMap H ((p : G) * x) ∈ quotientSupport H (eval H σ f.val) :=
    ⟨_, hp, rfl⟩
  rw [← hCq] at hpx
  obtain ⟨c, hc, hcx⟩ := hpx
  have hh : (p : G) * x * c⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcx)
  refine ⟨c, hc, Quotient.sound ?_⟩
  change QuotientGroup.rightRel P c x
  rw [QuotientGroup.rightRel_apply]
  have hm := P.mul_mem (P.inv_mem p.property) (hHP hh)
  simpa only [mul_assoc, inv_mul_cancel_left] using hm

private def stageExpand (f : CompactFunctions H σ) : CompactFunctions P ρP :=
  ⟨stageExpandSmooth H P hHP σ hH hP f,
    stageExpand_compact H P hHP σ hH hP f⟩

omit hH hP

omit [LocallyCompactSpace G] in
private def stageFlattenSmooth (F : CompactFunctions P ρP) : SmoothFunctions H σ := by
  let K := F.val.property.choose
  have hK := F.val.property.choose_spec
  refine smoothFunctionOf H σ
    (fun x => eval HP σP (eval P ρP F.val x).val 1) (fun h x => ?_)
    K (fun k x => ?_)
  · let p : P := ⟨h, hHP h.property⟩
    rw [show (h : G) = (p : G) from rfl, eval_covariant]
    change eval HP σP (eval P ρP F.val x).val (1 * p) =
      σ h (eval HP σP (eval P ρP F.val x).val 1)
    simpa [MonoidHom.comp_apply, Subgroup.subgroupOfEquivOfLe, p] using
      eval_covariant HP σP (eval P ρP F.val x).val ⟨p, h.property⟩ 1
  · exact congrArg (fun F' : EquivariantFunctions P ρP =>
      eval HP σP (F'.val x).val 1) (hK k)

omit [LocallyCompactSpace G] in
@[simp] private theorem stageFlattenSmooth_eval (F : CompactFunctions P ρP) (x : G) :
    eval H σ (stageFlattenSmooth H P hHP σ F) x =
      eval HP σP (eval P ρP F.val x).val 1 := rfl

include hH hP

private theorem stageFlatten_compact (F : CompactFunctions P ρP) :
    IsCompact (quotientSupport H (eval H σ (stageFlattenSmooth H P hHP σ F))) := by
  classical
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  have hHPc : IsClosed (HP : Set P) := hH.preimage continuous_subtype_val
  obtain ⟨C, hCc, hCq⟩ := leftQuotient_exists_isCompact_image P hP F.property
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  let S : Set (CompactFunctions HP σP) :=
    Set.range (fun c : C => eval P ρP F.val c)
  have hSf : S.Finite :=
    ((eval_isLocallyConstant P ρP F.val).comp_continuous continuous_subtype_val).range_finite
  choose D hDc hDq using fun v : CompactFunctions HP σP =>
    leftQuotient_exists_isCompact_image HP hHPc v.property
  let E : Set G := ⋃ v ∈ S,
    (fun z : P × G => (z.1 : G) * z.2) '' (D v ×ˢ C)
  have hEc : IsCompact E := hSf.isCompact_biUnion fun v _ =>
    ((hDc v).prod hCc).image
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
  apply (hEc.image (leftQuotient_isOpenQuotientMap H).continuous).of_isClosed_subset
    (isClosed_quotientSupport H σ (stageFlattenSmooth H P hHP σ F))
  rintro _ ⟨x, hx, rfl⟩
  have hxF : eval P ρP F.val x ≠ 0 := by
    intro hz
    apply hx
    change eval HP σP (eval P ρP F.val x).val 1 = 0
    rw [hz]
    rfl
  have hxq : quotientMap P x ∈ quotientSupport P (eval P ρP F.val) :=
    ⟨x, hxF, rfl⟩
  rw [← hCq] at hxq
  obtain ⟨c, hc, hcx⟩ := hxq
  have hpc : x * c⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hcx)
  let p : P := ⟨x * c⁻¹, hpc⟩
  have hxp : (p : G) * c = x := by simp [p, mul_assoc]
  have hp : eval HP σP (eval P ρP F.val c).val p ≠ 0 := by
    have he := congrArg
      (fun v : CompactFunctions HP σP => eval HP σP v.val 1)
      (eval_covariant P ρP F.val p c)
    change eval HP σP (eval P ρP F.val ((p : G) * c)).val 1 =
      eval HP σP (eval P ρP F.val c).val (1 * p) at he
    simp only [hxp, one_mul] at he
    intro hz
    exact hx (he.trans hz)
  have hpq : quotientMap HP p ∈
      quotientSupport HP (eval HP σP (eval P ρP F.val c).val) := ⟨p, hp, rfl⟩
  rw [← hDq] at hpq
  obtain ⟨d, hd, hdp⟩ := hpq
  have hpd : p * d⁻¹ ∈ HP := QuotientGroup.rightRel_apply.mp (Quotient.exact hdp)
  refine ⟨(d : G) * c, ?_, Quotient.sound ?_⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨eval P ρP F.val c, Set.mem_iUnion.mpr ?_⟩
    refine ⟨⟨⟨c, hc⟩, rfl⟩, ?_⟩
    exact ⟨(d, c), ⟨hd, hc⟩, rfl⟩
  · change QuotientGroup.rightRel H ((d : G) * c) x
    apply QuotientGroup.rightRel_apply.mpr
    have hm : (p : G) * (d : G)⁻¹ ∈ H := hpd
    simpa only [p, mul_inv_rev, mul_assoc] using hm

private def stageFlatten (F : CompactFunctions P ρP) : CompactFunctions H σ :=
  ⟨stageFlattenSmooth H P hHP σ F, stageFlatten_compact H P hHP σ hH hP F⟩

@[simp] private theorem stageFlatten_eval (F : CompactFunctions P ρP) (x : G) :
    eval H σ (stageFlatten H P hHP σ hH hP F).val x =
      eval HP σP (eval P ρP F.val x).val 1 := rfl

/-- Evaluation at the inner identity gives compact induction in stages. -/
def compactStagesEquiv : Representation.Equiv (compactInduced P ρP) (compactInduced H σ) where
  toFun := stageFlatten H P hHP σ hH hP
  invFun := stageExpand H P hHP σ hH hP
  map_add' F F' := by
    apply compact_ext
    intro x
    rfl
  map_smul' a F := by
    apply compact_ext
    intro x
    rfl
  left_inv F := by
    apply compact_ext
    intro x
    change stageInner H P hHP σ hH hP (stageFlatten H P hHP σ hH hP F) x =
      eval P ρP F.val x
    apply compact_ext
    intro p
    simp only [stageInner_eval, stageFlatten_eval, eval_covariant]
    change eval HP σP (eval P ρP F.val x).val (1 * p) =
      eval HP σP (eval P ρP F.val x).val p
    rw [one_mul]
  right_inv f := by
    apply compact_ext
    intro x
    change eval HP σP (stageInner H P hHP σ hH hP f x).val 1 = eval H σ f.val x
    simp only [stageInner_eval, Subgroup.coe_one, one_mul]
  isIntertwining' g := by
    apply LinearMap.ext
    intro F
    apply compact_ext
    intro x
    rfl

@[simp] theorem compactStagesEquiv_eval (F : CompactFunctions P ρP) (x : G) :
    eval H σ (compactStagesEquiv H P hHP σ hH hP F).val x =
      eval HP σP (eval P ρP F.val x).val 1 := rfl

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The stages equivalence commutes with every coefficient intertwiner. -/
theorem compactStagesEquiv_natural {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (F : CompactFunctions P ρP) :
    compactStagesEquiv H P hHP τ hH hP
      (compactInducedMap P (compactInducedMap HP (restrictAlongMap φ T)) F) =
    compactInducedMap H T (compactStagesEquiv H P hHP σ hH hP F) := by
  apply compact_ext
  intro x
  rfl

end Compact

private theorem locallyCompactOfBasis
    (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) :
    LocallyCompactSpace G := by
  obtain ⟨K, hKc, _⟩ := hBasis Set.univ isOpen_univ (Set.mem_univ 1)
  exact hKc.locallyCompactSpace_of_mem_nhds_of_group (K.isOpen.mem_nhds K.one_mem)

/-- The exact natural compact-induction-in-stages statement. -/
theorem compactInductionTransitivity : CompactInductionTransitivityStatement.{uG, uV} := by
  intro G _ _ _ _ hBasis H P hH hP hHP
  let : LocallyCompactSpace G := locallyCompactOfBasis hBasis
  refine ⟨fun A => compactStagesEquiv H P hHP A.representation hH hP, ?_, ?_⟩
  · intro A F x
    exact compactStagesEquiv_eval H P hHP A.representation hH hP F x
  · intro A B T F
    exact compactStagesEquiv_natural H P hHP A.representation hH hP (Langlands.SmoothRep.hom T) F

end Langlands.Induction
