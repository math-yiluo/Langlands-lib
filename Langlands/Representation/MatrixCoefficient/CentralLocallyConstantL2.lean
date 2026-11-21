import Langlands.Representation.MatrixCoefficient.CentralL2
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Square-integrable locally constant functions with central covariance -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Langlands.Induction

universe u

variable {G : Type u} [Group G]
  (χ : Subgroup.center G →* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)

/-- The actual covariant functions on `G` for the scalar central action. -/
abbrev CentralCovariantFunctions :=
  EquivariantFunctions (Subgroup.center G) (characterRepresentation χ)

/-- The norm of a centrally covariant function descends to the full central quotient. -/
def centralCovariantNorm (f : CentralCovariantFunctions χ) : G ⧸ Subgroup.center G → ℝ :=
  Quotient.lift (fun g => ‖f.val g‖) (by
    intro a b hab
    let z : Subgroup.center G := ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩
    have hzb : (z : G) * a = b := by
      rw [z.property.comm a]
      simp [z]
    have hf : f.val ((z : G) * a) = (χ z : ℂ) * f.val a := f.property z a
    rw [hzb] at hf
    rw [hf, norm_mul, hχ, one_mul])

@[simp]
theorem centralCovariantNorm_mk (f : CentralCovariantFunctions χ) (g : G) :
    centralCovariantNorm χ hχ f (QuotientGroup.mk g) = ‖f.val g‖ := rfl

section Topology

variable [TopologicalSpace G]

theorem centralCovariantNorm_isLocallyConstant (f : CentralCovariantFunctions χ)
    (hf : IsLocallyConstant f.val) : IsLocallyConstant (centralCovariantNorm χ hχ f) := by
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.leftRel (Subgroup.center G))).isCoinducing.isOpen_preimage.mp
  exact (hf.comp (fun z : ℂ => ‖z‖)) s

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G))

/-- The literal carrier of Renard IV.3.1, with pointwise local constancy and square integrability. -/
def centralLocallyConstantL2Submodule : Submodule ℂ (CentralCovariantFunctions χ) where
  carrier := {f | IsLocallyConstant f.val ∧ MemLp (centralCovariantNorm χ hχ f) 2 μ}
  zero_mem' := by
    refine ⟨IsLocallyConstant.const 0, ?_⟩
    have hZero : centralCovariantNorm χ hχ 0 = 0 := by
      funext q
      induction q using Quotient.inductionOn
      exact norm_zero
    rw [hZero]
    exact MemLp.zero
  add_mem' := by
    intro f h hf hh
    refine ⟨hf.1.comp₂ hh.1 (· + ·), ?_⟩
    apply (hf.2.add hh.2).mono'
      (centralCovariantNorm_isLocallyConstant χ hχ (f + h)
        (hf.1.comp₂ hh.1 (· + ·))).continuous.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    induction q using Quotient.inductionOn
    change |‖f.val _ + h.val _‖| ≤ ‖f.val _‖ + ‖h.val _‖
    rw [abs_of_nonneg (norm_nonneg _)]
    exact norm_add_le _ _
  smul_mem' := by
    intro a f hf
    refine ⟨hf.1.comp (fun z => a * z), ?_⟩
    have hNorm : centralCovariantNorm χ hχ (a • f) =
        fun q => ‖a‖ * centralCovariantNorm χ hχ f q := by
      funext q
      induction q using Quotient.inductionOn
      exact norm_mul _ _
    change MemLp (centralCovariantNorm χ hχ (a • f)) 2 μ
    rw [hNorm]
    exact hf.2.const_mul ‖a‖

/-- The actual locally constant central L² functions. -/
abbrev CentralLocallyConstantL2 := centralLocallyConstantL2Submodule χ hχ μ

variable [IsTopologicalGroup G] [μ.IsMulRightInvariant]

/-- Right translation preserves local constancy and square integrability. -/
def centralLocallyConstantL2Subrepresentation :
    Subrepresentation (equivariantAction (Subgroup.center G) (characterRepresentation χ)) where
  toSubmodule := centralLocallyConstantL2Submodule χ hχ μ
  apply_mem_toSubmodule := by
    intro g f hf
    refine ⟨hf.1.comp_continuous (continuous_mul_const g), ?_⟩
    let ρ := equivariantAction (Subgroup.center G) (characterRepresentation χ)
    have hNorm : centralCovariantNorm χ hχ (ρ g f) =
        centralCovariantNorm χ hχ f ∘ (fun q => q * QuotientGroup.mk g) := by
      funext q
      induction q using Quotient.inductionOn
      rfl
    change MemLp (centralCovariantNorm χ hχ (ρ g f)) 2 μ
    rw [hNorm]
    exact hf.2.comp_measurePreserving (measurePreserving_mul_right μ (QuotientGroup.mk g))

/-- The actual right regular action on the locally constant central L² space. -/
def centralLocallyConstantL2Representation :
    Representation ℂ G (CentralLocallyConstantL2 χ hχ μ) :=
  (centralLocallyConstantL2Subrepresentation χ hχ μ).toRepresentation

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    [IsTopologicalGroup G] in
theorem centralCovariantNorm_eq_centralNorm (f : CentralFunctions χ) :
    centralCovariantNorm χ hχ f.val = centralNorm χ hχ f := by
  funext q
  induction q using Quotient.inductionOn
  rfl

/-- Forget the uniform right stabilizer, keeping the same underlying function. -/
def centralL2ToLocallyConstant :
    (centralL2Representation χ hχ μ).IntertwiningMap
      (centralLocallyConstantL2Representation χ hχ μ) where
  toLinearMap :=
    { toFun := fun f => ⟨f.val.val, eval_isLocallyConstant _ _ f.val, by
        rw [centralCovariantNorm_eq_centralNorm]
        exact f.property⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  isIntertwining' _ := by ext f; rfl

theorem centralL2ToLocallyConstant_injective :
    Function.Injective (centralL2ToLocallyConstant χ hχ μ) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun F : CentralLocallyConstantL2 χ hχ μ => F.val) h

/-- The published uniform model is exactly the smooth part of the literal model. -/
theorem centralL2ToLocallyConstant_range :
    (centralL2ToLocallyConstant χ hχ μ).range.toSubmodule =
      smoothVectors (R := ℂ) (G := G) (V := CentralLocallyConstantL2 χ hχ μ)
        (centralLocallyConstantL2Representation χ hχ μ) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact isSmoothVector_map _ (centralL2Representation_smooth χ hχ μ g)
  · intro hf
    obtain ⟨K, hK⟩ := hf
    let g : CentralFunctions χ := ⟨f.val, ⟨K, fun k => congrArg Subtype.val (hK k)⟩⟩
    have hg : MemLp (centralNorm χ hχ g) 2 μ := by
      rw [← centralCovariantNorm_eq_centralNorm]
      exact f.property.2
    exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

end Topology

end Langlands.Induction
