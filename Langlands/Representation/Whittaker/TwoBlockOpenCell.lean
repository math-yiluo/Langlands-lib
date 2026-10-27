import Langlands.Representation.Shahidi.Induction

/-!
# The concrete two-block cell of JPSS Proposition 9.1

For positive ranks `A = a + 1` and `B = b + 1`, the cell `P w U'` of `GL_(A+B)`,
the restriction of the literal ordered canonical normalized upper induction of
`(π₁, π₂)` to the representatives `w n(x)`, and the submodule of induced
functions supported in the cell with compactly supported restriction. These
are concrete definitions and elementary laws only.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV

section Cell

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)

/-- The ordered shape `(A, B) = (a + 1, b + 1)`, literally `Shahidi.twoBlocks`. -/
abbrev twoBlockShape : BlockShape (a + 1 + (b + 1)) :=
  Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b)

/-- The actual standard upper parabolic `P` of the ordered shape `(A, B)`. -/
abbrev twoBlockParabolic : Subgroup (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :=
  (twoBlockShape a b).parabolic F.Carrier

/-- The representative `w n(x)`: the all-positive block Weyl matrix times the
exchanged radical `U'(x)`, for `x` with `B` rows and `A` columns. -/
def twoBlockCellPoint (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier :=
  Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
    Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x

/-- The cell `C = P w U'` of all products `q w n(x)` with `q ∈ P`. -/
def twoBlockCell : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :=
  {g | ∃ q : twoBlockParabolic F a b, ∃ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier,
    g = (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) *
      Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
        Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x}

theorem mem_twoBlockCell_iff (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :
    g ∈ twoBlockCell F a b ↔
      ∃ q : twoBlockParabolic F a b, ∃ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier,
        g = (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) *
          Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
            Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x :=
  Iff.rfl

/-- Every displayed product `q w n(x)` lies in the cell. -/
theorem parabolic_mul_mem_twoBlockCell (q : twoBlockParabolic F a b)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) *
        Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
          Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x ∈
      twoBlockCell F a b :=
  ⟨q, x, rfl⟩

/-- Each representative `w n(x)` lies in the cell. -/
theorem twoBlockCellPoint_mem (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    twoBlockCellPoint F a b x ∈ twoBlockCell F a b :=
  ⟨1, x, by rw [twoBlockCellPoint, OneMemClass.coe_one, one_mul]⟩

/-- The Weyl representative itself is the point `x = 0` of the cell. -/
theorem blockWeyl_mem_twoBlockCell :
    Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier ∈ twoBlockCell F a b := by
  simpa [twoBlockCellPoint] using twoBlockCellPoint_mem F a b 0

/-- Left `P`-invariance of the cell. -/
theorem mul_mem_twoBlockCell {q g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier}
    (hq : q ∈ twoBlockParabolic F a b) (hg : g ∈ twoBlockCell F a b) :
    q * g ∈ twoBlockCell F a b := by
  obtain ⟨r, x, rfl⟩ := hg
  exact ⟨⟨q, hq⟩ * r, x, by simp only [Subgroup.coe_mul, mul_assoc]⟩

/-- Left multiplication by an element of `P` neither adds nor removes points. -/
theorem mul_mem_twoBlockCell_iff (q : twoBlockParabolic F a b)
    (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :
    (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) * g ∈ twoBlockCell F a b ↔
      g ∈ twoBlockCell F a b := by
  refine ⟨fun h => ?_, mul_mem_twoBlockCell F a b q.property⟩
  have h' := mul_mem_twoBlockCell F a b (q⁻¹).property h
  rwa [Subgroup.coe_inv, inv_mul_cancel_left] at h'

end Cell

section Induction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
  (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)

/-- The literal ordered representation `ξ` of the parent statement. -/
abbrev twoBlockInduced :=
  F.canonicalNormalizedProductInduced (twoBlockShape a b) (Shahidi.pairFamily π₁ π₂)

theorem twoBlockInduced_eq :
    twoBlockInduced F a b π₁ π₂ =
      F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂) :=
  rfl

/-- The actual inducing representation of `P` on `V₁ ⊗ V₂`: the block tensor
through the Levi projection, twisted by the positive half modulus. -/
abbrev twoBlockInducingRepresentation :
    Representation ℂ (twoBlockParabolic F a b) (PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) :=
  twist (F.canonicalTopologicalData.parabolicHalfModulus (twoBlockShape a b))
    (((twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂)).comp
      ((twoBlockShape a b).leviProjection F.Carrier))

/-- The carrier of `ξ`: the actual smooth covariant functions. -/
abbrev TwoBlockInducedCarrier :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1 + (b + 1))
  Induction.SmoothFunctions (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂)

/-- Evaluation of an element of the carrier of `ξ`, by `Induction.eval`. -/
def twoBlockEval (f : TwoBlockInducedCarrier F a b π₁ π₂)
    (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :
    PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1 + (b + 1))
  Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂) f g

theorem twoBlockEval_eq (f : TwoBlockInducedCarrier F a b π₁ π₂)
    (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1 + (b + 1))
    twoBlockEval F a b π₁ π₂ f g =
      Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂) f g :=
  rfl

/-- `ξ` acts by right translation. -/
theorem twoBlockEval_twoBlockInduced (h g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier)
    (f : TwoBlockInducedCarrier F a b π₁ π₂) :
    twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ h f) g =
      twoBlockEval F a b π₁ π₂ f (g * h) :=
  rfl

/-- The complex-linear restriction `f ↦ (x ↦ f(w n(x)))` to all tensor-valued
functions of `x`. -/
def twoBlockRestriction :
    TwoBlockInducedCarrier F a b π₁ π₂ →ₗ[ℂ]
      (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier →
        PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) where
  toFun f x := twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem twoBlockRestriction_apply (f : TwoBlockInducedCarrier F a b π₁ π₂)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1 + (b + 1))
    twoBlockRestriction F a b π₁ π₂ f x =
      Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂) f
        (Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
          Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x) :=
  rfl

/-- The submodule `D`: induced functions whose support lies in the cell and
whose restriction to the representatives has compact support. -/
def twoBlockCellSubmodule : Submodule ℂ (TwoBlockInducedCarrier F a b π₁ π₂) :=
  letI := F.canonicalTopologicalData.topology
  { carrier := {f | Function.support (twoBlockEval F a b π₁ π₂ f) ⊆ twoBlockCell F a b ∧
      HasCompactSupport (twoBlockRestriction F a b π₁ π₂ f)}
    zero_mem' := by
      refine ⟨fun g hg => (hg rfl).elim, ?_⟩
      rw [map_zero]
      exact HasCompactSupport.zero
    add_mem' := by
      rintro f h ⟨hf, hf'⟩ ⟨hh, hh'⟩
      refine ⟨(Function.support_add _ _).trans (Set.union_subset hf hh), ?_⟩
      rw [map_add]
      exact hf'.add hh'
    smul_mem' := by
      rintro c f ⟨hf, hf'⟩
      refine ⟨(Function.support_const_smul_subset c _).trans hf, ?_⟩
      rw [map_smul]
      exact hf'.mono (Function.support_const_smul_subset c _) }

/-- Membership in `D` is exactly the two defining conditions. -/
theorem mem_twoBlockCellSubmodule_iff (f : TwoBlockInducedCarrier F a b π₁ π₂) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (a + 1 + (b + 1))
    f ∈ twoBlockCellSubmodule F a b π₁ π₂ ↔
      (∀ g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier,
        Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂)
          f g ≠ 0 → g ∈ twoBlockCell F a b) ∧
      HasCompactSupport (fun x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier =>
        Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂) f
          (Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier *
            Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x)) :=
  Iff.rfl

/-- The injective linear inclusion `D → ξ`. -/
def twoBlockCellInclusion :
    twoBlockCellSubmodule F a b π₁ π₂ →ₗ[ℂ] TwoBlockInducedCarrier F a b π₁ π₂ :=
  (twoBlockCellSubmodule F a b π₁ π₂).subtype

@[simp] theorem twoBlockCellInclusion_apply (f : twoBlockCellSubmodule F a b π₁ π₂) :
    twoBlockCellInclusion F a b π₁ π₂ f = f.val :=
  rfl

theorem twoBlockCellInclusion_injective :
    Function.Injective (twoBlockCellInclusion F a b π₁ π₂) :=
  Subtype.val_injective

/-- The restriction map on `D`. -/
def twoBlockCellRestriction :
    twoBlockCellSubmodule F a b π₁ π₂ →ₗ[ℂ]
      (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier →
        PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) :=
  (twoBlockRestriction F a b π₁ π₂).comp (twoBlockCellInclusion F a b π₁ π₂)

theorem twoBlockCellRestriction_apply (f : twoBlockCellSubmodule F a b π₁ π₂)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    twoBlockCellRestriction F a b π₁ π₂ f x =
      twoBlockEval F a b π₁ π₂ f.val (twoBlockCellPoint F a b x) :=
  rfl

/-- An element of `D` vanishes off the cell. -/
theorem twoBlockEval_eq_zero_of_not_mem (f : twoBlockCellSubmodule F a b π₁ π₂)
    {g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier} (hg : g ∉ twoBlockCell F a b) :
    twoBlockEval F a b π₁ π₂ f.val g = 0 :=
  Function.notMem_support.mp fun h => hg (f.property.1 h)

/-- The restriction of an element of `D` has compact support. -/
theorem hasCompactSupport_twoBlockCellRestriction (f : twoBlockCellSubmodule F a b π₁ π₂) :
    letI := F.canonicalTopologicalData.topology
    HasCompactSupport (twoBlockCellRestriction F a b π₁ π₂ f) :=
  f.property.2

end Induction

end Langlands.Whittaker
