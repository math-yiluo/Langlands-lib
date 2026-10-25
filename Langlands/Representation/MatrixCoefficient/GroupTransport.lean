import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Central quotients and coefficient norms under topological group equivalences

Internal constructions on the actual centers and quotient groups. Pullback keeps
the representation carrier, algebraic functional, and vector unchanged.
-/

noncomputable section

namespace Langlands

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- The actual quotient equivalence induced by a continuous group equivalence. -/
def centralQuotientCongr (e : H ≃ₜ* G) :
    (H ⧸ Subgroup.center H) ≃ₜ* (G ⧸ Subgroup.center G) where
  toMulEquiv := QuotientGroup.congr (Subgroup.center H) (Subgroup.center G)
    e.toMulEquiv (Subgroup.map_center_eq e.toMulEquiv)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (Subgroup.center H)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp e.continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp e.symm.continuous

@[simp]
theorem centralQuotientCongr_mk (e : H ≃ₜ* G) (h : H) :
    centralQuotientCongr e (QuotientGroup.mk h) = QuotientGroup.mk (e h) := rfl

@[simp]
theorem centralQuotientCongr_symm (e : H ≃ₜ* G) :
    (centralQuotientCongr e).symm = centralQuotientCongr e.symm := by
  ext q
  induction q using Quotient.inductionOn
  rfl

namespace UnitaryCentralCharacter

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- Pull back the central character through the actual restriction to the center. -/
def compContinuousMulEquiv (c : UnitaryCentralCharacter ρ) (e : H ≃ₜ* G) :
    UnitaryCentralCharacter (ρ.comp e.toMonoidHom) where
  character := c.character.comp (Subgroup.centerCongr e.toMulEquiv).toMonoidHom
  isOpen_ker := by
    have hc : Continuous (Subgroup.centerCongr e.toMulEquiv) :=
      (e.continuous.comp continuous_subtype_val).subtype_mk _
    exact c.isOpen_ker.preimage hc
  norm_eq_one z := c.norm_eq_one (Subgroup.centerCongr e.toMulEquiv z)
  acts z v := c.acts (Subgroup.centerCongr e.toMulEquiv z) v

@[simp]
theorem compContinuousMulEquiv_character (c : UnitaryCentralCharacter ρ)
    (e : H ≃ₜ* G) (z : Subgroup.center H) :
    (c.compContinuousMulEquiv e).character z =
      c.character (Subgroup.centerCongr e.toMulEquiv z) := rfl

/-- The actual descended norm is precomposed with the central quotient map. -/
theorem coefficientNorm_compContinuousMulEquiv (c : UnitaryCentralCharacter ρ)
    (e : H ≃ₜ* G) (ℓ : Module.Dual ℂ V) (v : V) :
    (c.compContinuousMulEquiv e).coefficientNorm ℓ v =
      c.coefficientNorm ℓ v ∘ centralQuotientCongr e := by
  funext q
  induction q using Quotient.inductionOn
  rfl

end UnitaryCentralCharacter

end Langlands
