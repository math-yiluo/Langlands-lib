import Langlands.Group.LeftQuotient

/-!
# Left homogeneous quotients

`LeftCosetSpace Γ` is the space `Γ \ H`, with positive right translation.
No normality hypothesis on `Γ` is used.
-/

universe u v

open Topology

namespace Langlands.Global

variable {H : Type u} [Group H]

/-- The left homogeneous quotient `Γ \ H`: representatives differ by left multiplication. -/
abbrev LeftCosetSpace (Γ : Subgroup H) :=
  Langlands.Induction.LeftQuotient Γ

namespace LeftCosetSpace

variable (Γ : Subgroup H)

/-- The projection to the left homogeneous quotient. -/
def mk (x : H) : LeftCosetSpace Γ := Langlands.Induction.quotientMap Γ x

theorem mk_surjective : Function.Surjective (mk Γ) :=
  Quotient.mk_surjective

@[simp]
theorem mk_eq_mk_iff (x y : H) :
    mk Γ x = mk Γ y ↔ y * x⁻¹ ∈ Γ := by
  exact Quotient.eq.trans QuotientGroup.rightRel_apply

@[simp]
theorem mk_subgroup_mul (γ : Γ) (x : H) :
    mk Γ ((γ : H) * x) = mk Γ x := by
  apply (mk_eq_mk_iff Γ _ _).mpr
  simp

/-- Positive right translation on points of `Γ \ H`. -/
def rightTranslate (g : H) : LeftCosetSpace Γ → LeftCosetSpace Γ :=
  Langlands.Induction.quotientRight Γ g

@[simp]
theorem rightTranslate_mk (g x : H) :
    rightTranslate Γ g (mk Γ x) = mk Γ (x * g) := rfl

@[simp]
theorem rightTranslate_one (q : LeftCosetSpace Γ) :
    rightTranslate Γ 1 q = q := by
  induction q using Quotient.inductionOn with
  | _ x => simp [rightTranslate, Langlands.Induction.quotientRight]

theorem rightTranslate_mul (g h : H) (q : LeftCosetSpace Γ) :
    rightTranslate Γ h (rightTranslate Γ g q) = rightTranslate Γ (g * h) q := by
  induction q using Quotient.inductionOn with
  | _ x => exact congrArg (mk Γ) (mul_assoc x g h)

/-- Right translation on points is a left action of the opposite group. -/
instance : MulAction Hᵐᵒᵖ (LeftCosetSpace Γ) where
  smul g := rightTranslate Γ (MulOpposite.unop g)
  one_smul := rightTranslate_one Γ
  mul_smul g h q := (rightTranslate_mul Γ (MulOpposite.unop h)
    (MulOpposite.unop g) q).symm

@[simp]
theorem op_smul (g : H) (q : LeftCosetSpace Γ) :
    MulOpposite.op g • q = rightTranslate Γ g q := rfl

/-- Pullback along positive right translation gives the positive left action on functions. -/
@[instance_reducible]
def rightRegularAction (E : Type v) : MulAction H (LeftCosetSpace Γ → E) where
  smul g f q := f (rightTranslate Γ g q)
  one_smul f := by
    funext q
    change f (rightTranslate Γ 1 q) = f q
    rw [rightTranslate_one]
  mul_smul g h f := by
    funext q
    exact congrArg f (rightTranslate_mul Γ g h q).symm

/-- A left-`Γ`-invariant function descends to the actual quotient. -/
def lift {E : Type v} (f : H → E)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) :
    LeftCosetSpace Γ → E :=
  Langlands.QuotientIntegration.descend Γ f hf

@[simp]
theorem lift_mk {E : Type v} (f : H → E)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) (x : H) :
    lift Γ f hf (mk Γ x) = f x := rfl

/-- Quotient functions are exactly functions invariant under left multiplication by `Γ`. -/
def functionEquiv (E : Type v) :
    (LeftCosetSpace Γ → E) ≃
      {f : H → E // ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x} where
  toFun f := ⟨fun x => f (mk Γ x), fun γ x => congrArg f (mk_subgroup_mul Γ γ x)⟩
  invFun f := lift Γ f.val f.property
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  right_inv f := by
    apply Subtype.ext
    rfl

section Topology

variable [TopologicalSpace H]

theorem continuous_mk : Continuous (mk Γ) := continuous_quotient_mk'

theorem isQuotientMap_mk : IsQuotientMap (mk Γ) := isQuotientMap_quotient_mk'

theorem continuous_iff {E : Type v} [TopologicalSpace E]
    {f : LeftCosetSpace Γ → E} :
    Continuous f ↔ Continuous (f ∘ mk Γ) :=
  (isQuotientMap_mk Γ).continuous_iff

theorem continuous_lift {E : Type v} [TopologicalSpace E] (f : H → E)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x)
    (hc : Continuous f) : Continuous (lift Γ f hf) :=
  (continuous_iff Γ).mpr hc

variable [IsTopologicalGroup H]

/-- The inversion comparison with Mathlib's right homogeneous quotient `H / Γ`. -/
def invHomeomorph : LeftCosetSpace Γ ≃ₜ H ⧸ Γ where
  toEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ
  continuous_toFun := by
    apply (continuous_iff Γ).mpr
    exact QuotientGroup.continuous_mk.comp continuous_inv
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
    exact (continuous_mk Γ).comp continuous_inv

@[simp]
theorem invHomeomorph_mk (x : H) :
    invHomeomorph Γ (mk Γ x) = QuotientGroup.mk x⁻¹ := rfl

@[simp]
theorem invHomeomorph_symm_mk (x : H) :
    (invHomeomorph Γ).symm (QuotientGroup.mk x) = mk Γ x⁻¹ := rfl

theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk Γ) :=
  Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap Γ

theorem continuous_rightTranslate (g : H) : Continuous (rightTranslate Γ g) := by
  apply (continuous_iff Γ).mpr
  exact (continuous_mk Γ).comp (continuous_id.mul_const g)

/-- Every right translation is a homeomorphism with inverse translation by the inverse. -/
def rightTranslateHomeomorph (g : H) : LeftCosetSpace Γ ≃ₜ LeftCosetSpace Γ :=
  Langlands.QuotientIntegration.rightTranslate Γ g

instance : ContinuousSMul Hᵐᵒᵖ (LeftCosetSpace Γ) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_mk Γ)).continuous_comp_iff]
    exact (continuous_mk Γ).comp
      (continuous_snd.mul (MulOpposite.continuous_unop.comp continuous_fst))

instance [LocallyCompactSpace H] : LocallyCompactSpace (LeftCosetSpace Γ) :=
  Langlands.QuotientIntegration.leftQuotient_locallyCompactSpace Γ

instance [SecondCountableTopology H] : SecondCountableTopology (LeftCosetSpace Γ) :=
  ContinuousConstSMul.secondCountableTopology

instance [IsClosed (Γ : Set H)] : T2Space (LeftCosetSpace Γ) :=
  Langlands.QuotientIntegration.leftQuotient_t2Space Γ inferInstance

end Topology

end LeftCosetSpace
end Langlands.Global
