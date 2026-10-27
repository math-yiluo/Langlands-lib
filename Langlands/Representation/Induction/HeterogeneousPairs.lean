import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Category.UniverseLift

/-! Literal carrier lifts and equivalences of normalized two-block products. -/

noncomputable section

namespace Langlands

universe uG uV uW uX

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The literal conjugation used by heterogeneous pair induction is the pointwise lift. -/
theorem literalULiftRepresentation_eq (ρ : Representation ℂ G V) :
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ =
      universeLiftRepresentation.{uX} ρ := by
  ext g v
  rfl

/-- The original action and the literal ULift conjugation are equivalent via `up`. -/
def literalULiftEquiv (ρ : Representation ℂ G V) :
    ρ.Equiv ((ULift.moduleEquiv (R := ℂ) (M := V)).symm.conjRingEquiv.toMonoidHom.comp ρ :
      Representation ℂ G (ULift.{uX} V)) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun _ => by
    ext v
    rfl

@[simp] theorem literalULiftEquiv_apply (ρ : Representation ℂ G V) (v : V) :
    literalULiftEquiv.{uG,uV,uX} ρ v = ULift.up v := rfl

@[simp] theorem literalULiftEquiv_symm_apply (ρ : Representation ℂ G V)
    (v : ULift.{uX} V) :
    (literalULiftEquiv ρ).symm v = v.down := rfl

/-- Smoothness is unchanged by the exact conjugation expression used in the target. -/
theorem isSmooth_literalULift_iff [TopologicalSpace G] (ρ : Representation ℂ G V) :
    IsSmooth ((ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ :
      Representation ℂ G (ULift.{uX} V)) ↔ IsSmooth ρ := by
  rw [literalULiftRepresentation_eq]
  exact isSmooth_universeLift_iff ρ

/-- Precomposition of both actions preserves the same linear equivalence. -/
def _root_.Representation.Equiv.precomp {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ)
    {H : Type uX} [Group H] (f : H →* G) :
    Representation.Equiv (ρ.comp f) (τ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => e.isIntertwining' (f h)

end Langlands

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Shahidi

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
variable {V₀ V₁ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
  [AddCommGroup V₁] [Module ℂ V₁]
variable {W₀ W₁ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
  [AddCommGroup W₁] [Module ℂ W₁]
variable {ρ₀ : Representation ℂ (GeneralLinear a F.Carrier) V₀}
  {ρ₁ : Representation ℂ (GeneralLinear b F.Carrier) V₁}
variable {τ₀ : Representation ℂ (GeneralLinear a F.Carrier) W₀}
  {τ₁ : Representation ℂ (GeneralLinear b F.Carrier) W₁}

/-- Two arbitrary factor equivalences give an equivalence of the literal actual
normalized pair inductions, even across different carrier universes. -/
def normalizedPairInducedEquiv (e₀ : ρ₀.Equiv τ₀) (e₁ : ρ₁.Equiv τ₁) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    (T.normalizedProductInduced (twoBlocks a b ha hb) (pairFamily ρ₀ ρ₁)).Equiv
      (T.normalizedProductInduced (twoBlocks a b ha hb) (pairFamily τ₀ τ₁)) := by
  apply T.normalizedProductInducedEquiv
  exact Fin.cases e₀ (Fin.cases e₁ finZeroElim)

end Langlands.PadicField.TopologicalData
