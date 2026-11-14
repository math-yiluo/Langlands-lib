import Langlands.Representation.Whittaker.TwoBlockCellSectionProof
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
import Langlands.AllField.Representation.Whittaker.TwoBlockCellSectionStatement
/-!
# Proof of the two-block cell sections

For smooth `π₁`, `π₂`, every function `x ↦ Ψ(x) v` is the restriction
`x ↦ f(w n(x))` of an element `f` of the cell submodule `D`. The function
`q ↦ Ψ(lowerCoordinates q) v` on the opposite radical `Q` is extended from the
open `P`-orbit of the base coset by the Library's orbit-section extension, and
the result is right translated by `w⁻¹`. Openness of `P Q` comes from the block
Iwahori factorization.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellSectionStatement TwoBlockInducedCarrier exists_openSubgroup_subset_parabolic_mul_opposite hasCompactSupport_twoBlockCellRestriction oppositeLower twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSection twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV u

section Lower


end Lower

section Topology

end Topology

section Invariance


end Invariance

private theorem fieldTotallyDisconnected 
    {F : Type uF} [Field F] (T : LocalFieldData F) :
    letI := T.topology
    TotallyDisconnectedSpace F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

section Cell

variable (F : Type uF) [Field F] (a b : ℕ)

/-- The point `w n(x) w⁻¹` of the opposite radical with lower-left block `x`. -/
def oppositeLower (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
    (twoBlockShape a b).oppositeUnipotentSubgroup F :=
  ⟨Shahidi.lower (a + 1) (b + 1) F x,
    lower_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b)
      F x⟩

/-- The block Iwahori factorization puts an open subgroup inside `P Q`. -/
theorem exists_openSubgroup_subset_parabolic_mul_opposite [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∃ K : OpenSubgroup (Langlands.GeneralLinear (a + 1 + (b + 1)) F),
      ∀ k ∈ K, ∃ p ∈ twoBlockParabolic F a b,
        ∃ q ∈ (twoBlockShape a b).oppositeUnipotentSubgroup F, k = p * q := by
  obtain ⟨K, -, -, hK⟩ :=
    (Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization (twoBlockShape a b))
      (⟨⟩ : LocalFieldData F) (U := Set.univ) Filter.univ_mem
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨⟨l, m, u⟩, hlmu⟩ :=
    (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.bijective _ _ hK).2 ⟨k⁻¹, K.inv_mem hk⟩
  have hk' : l.val * m.val * u.val = k⁻¹ := congrArg Subtype.val hlmu
  have hl := ((twoBlockShape a b).mem_iwahoriLower F K.toSubgroup l.val).mp l.property
  have hm := ((twoBlockShape a b).mem_iwahoriLevi F K.toSubgroup m.val).mp m.property
  have hu := ((twoBlockShape a b).mem_iwahoriUpper F K.toSubgroup u.val).mp u.property
  rw [BlockShape.unipotentSubgroup, Subgroup.mem_map] at hu
  rw [BlockShape.leviSubgroup, MonoidHom.mem_range] at hm
  obtain ⟨u', -, hu'⟩ := hu.2
  obtain ⟨m', hm'⟩ := hm.2
  refine ⟨u.val⁻¹ * m.val⁻¹, (twoBlockParabolic F a b).mul_mem
      ((twoBlockParabolic F a b).inv_mem ?_) ((twoBlockParabolic F a b).inv_mem ?_),
    l.val⁻¹, ((twoBlockShape a b).oppositeUnipotentSubgroup F).inv_mem hl.2, ?_⟩
  · rw [← hu']
    exact u'.property
  · rw [← hm']
    exact ((twoBlockShape a b).leviInParabolic F m').property
  · rw [← inv_inv k, ← hk']
    group

end Cell

/-- JPSS (9.1), section step: every `x ↦ Ψ(x) v` is the restriction of an element
of the cell submodule. -/
theorem twoBlockCellSection : TwoBlockCellSectionStatement.{uF, uV} := by
  intro F _ _ _ _ a b V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ Ψ v
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := fieldTotallyDisconnected T
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  let := T.generalLinearNonarchimedean (a + 1 + (b + 1))
  let := T.generalLinearLocallyCompactSpace (a + 1 + (b + 1))
  let := T.generalLinearT2Space (a + 1 + (b + 1))
  let := T.generalLinearSigmaCompactSpace (a + 1 + (b + 1))
  let : TotallyDisconnectedSpace (Matrix (Fin (b + 1)) (Fin (a + 1)) F) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin (b + 1) → Fin (a + 1) → F))
  let : LocallyCompactSpace (Matrix (Fin (b + 1)) (Fin (a + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (b + 1) → Fin (a + 1) → F))
  let P := twoBlockParabolic F a b
  let Q := (twoBlockShape a b).oppositeUnipotentSubgroup F
  let w := Shahidi.blockWeyl (a + 1) (b + 1) F
  have hP : IsClosed (P : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F)) :=
    (twoBlockShape a b).isClosed_parabolic F
  have hQ : IsClosed (Q : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F)) :=
    (twoBlockShape a b).isClosed_oppositeUnipotentSubgroup F
  have hρ : IsSmooth (twoBlockInducingRepresentation F a b π₁ π₂) :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus (twoBlockShape a b))).2
      (isSmooth_comp _ ((twoBlockShape a b).leviProjectionContinuous F).continuous
        (Shahidi.isSmooth_pairRepresentation (Nat.succ_pos a) (Nat.succ_pos b) hπ₁ hπ₂))
  let A : Induction.SmoothRep.{0, uF, uV} ℂ P :=
    Langlands.SmoothRep.of (twoBlockInducingRepresentation F a b π₁ π₂) hρ
  let S := Geometric.orbitStabilizer P Q 1
  let σ := A.obj.ρ.comp (Geometric.stabilizerToInducing P Q 1)
  have hS : ∀ s : S, s = 1 := by
    intro s
    have hs := (Geometric.stabilizerToInducing P Q 1 s).property
    rw [Geometric.stabilizerToInducing_apply, inv_one, one_mul, mul_one] at hs
    exact Subtype.ext (Subtype.ext
      (eq_one_of_mem_parabolic_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1)
        (Nat.succ_pos a) (Nat.succ_pos b) F hs s.val.property))
  let f0 : Q → PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) :=
    fun q => Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1) q.val) • v
  have hcov : ∀ (s : S) (q : Q), f0 ((s : Q) * q) = σ s (f0 q) := by
    intro s q
    rw [hS s]
    simp
  obtain ⟨H, hH⟩ := SchwartzBruhat.exists_openSubgroup_invariant Ψ
  have hcoord : Continuous (oppositeCoordinateHom (a + 1) (b + 1) (Nat.succ_pos a)
      (Nat.succ_pos b) F) :=
    continuous_ofAdd.comp
      ((Shahidi.continuous_lowerCoordinates (a + 1) (b + 1)).comp continuous_subtype_val)
  let K : OpenSubgroup Q := H.comap _ hcoord
  have hK : ∀ (k : K) (q : Q), f0 (q * (k : Q)) = f0 q := by
    intro k q
    simp only [f0, Subgroup.coe_mul]
    rw [lowerCoordinates_mul (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b) F
      q.property (k : Q).property]
    exact congrArg (· • v) (hH _ k.property _)
  have hsupp : Function.support f0 =
      oppositeLower F a b '' Function.support (fun x => Ψ x • v) := by
    ext q
    constructor
    · intro hq
      refine ⟨Shahidi.lowerCoordinates (a + 1) (b + 1) q.val, hq, Subtype.ext ?_⟩
      exact (eq_lower_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a)
        (Nat.succ_pos b) F q.property).symm
    · rintro ⟨x, hx, rfl⟩
      change Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1)
        (Shahidi.lower (a + 1) (b + 1) F x)) • v ≠ 0
      rwa [Shahidi.lowerCoordinates_lower]
  have hφ : IsCompact (Function.support (fun x => Ψ x • v)) := by
    have hlc : IsLocallyConstant (fun x => Ψ x • v) :=
      Ψ.locallyConstant.comp (fun c : ℂ => c • v)
    exact (Ψ.hasCompactSupport.smul_right (f' := fun _ => v)).isCompact.of_isClosed_subset
      (hlc.isOpen_fiber 0).isClosed_compl (subset_tsupport _)
  have hc : IsCompact (Induction.quotientSupport S f0) := by
    rw [Induction.quotientSupport, hsupp, Set.image_image]
    refine hφ.image ?_
    exact continuous_quotient_mk'.comp
      ((Shahidi.continuous_lower (a + 1) (b + 1) F).subtype_mk _)
  let g := Induction.compactFunctionOf S σ f0 hcov K hK hc
  have hU : IsOpen (Geometric.cosetOrbit P Q 1) := by
    obtain ⟨K₀, hK₀⟩ := exists_openSubgroup_subset_parabolic_mul_opposite F a b
    exact isOpen_cosetOrbit_one P Q (isOpen_mul_of_openSubgroup P Q K₀ hK₀)
  have hZ : IsClosed ((fun x : Geometric.cosetOrbit P Q 1 =>
      (x : Induction.LeftQuotient P)) ⁻¹' Geometric.cosetOrbit P Q 1) := by
    rw [Subtype.coe_preimage_self]
    exact isClosed_univ
  obtain ⟨f, hfU, hfQ⟩ := Geometric.closedOrbitSectionExtension.{uF, uV}
    (Langlands.GeneralLinear (a + 1 + (b + 1)) F) P Q hP hQ 1
    (Geometric.cosetOrbit P Q 1) hU subset_rfl hZ A g
  let f' : TwoBlockInducedCarrier F a b π₁ π₂ := twoBlockInduced F a b π₁ π₂ w⁻¹ f.val
  have hrestr : ∀ x, twoBlockRestriction F a b π₁ π₂ f' x = Ψ x • v := by
    intro x
    calc twoBlockRestriction F a b π₁ π₂ f' x
        = Induction.eval P A.obj.ρ f.val (1⁻¹ * (oppositeLower F a b x : _)) := by
          rw [inv_one, one_mul]
          rfl
      _ = f0 (oppositeLower F a b x) := hfQ _
      _ = Ψ x • v := by
          change Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1)
            (Shahidi.lower (a + 1) (b + 1) F x)) • v = Ψ x • v
          rw [Shahidi.lowerCoordinates_lower]
  refine ⟨f', ⟨?_, ?_⟩, hrestr⟩
  · intro x hx
    have hx' : Induction.eval P A.obj.ρ f.val (x * w⁻¹) ≠ 0 := hx
    obtain ⟨q, hq⟩ := hfU _ hx'
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    rw [inv_one, one_mul] at hr
    have hq' := eq_lower_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a)
      (Nat.succ_pos b) F q.property
    have key : ∀ y, (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F) =
        w * Shahidi.intertwiningUnipotent (a + 1) (b + 1) F y * w⁻¹ →
        x = x * w⁻¹ * (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F)⁻¹ * w *
          Shahidi.intertwiningUnipotent (a + 1) (b + 1) F y := by
      intro y hy
      rw [hy]
      group
    exact ⟨⟨_, hr⟩, _, key _ hq'⟩
  · rw [show twoBlockRestriction F a b π₁ π₂ f' = fun x => Ψ x • v from funext hrestr]
    exact Ψ.hasCompactSupport.smul_right

end Langlands.AllField.Whittaker
