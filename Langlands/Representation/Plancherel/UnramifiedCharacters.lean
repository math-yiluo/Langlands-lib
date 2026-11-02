import Langlands.Representation.Twist.ContinuousCharacterProof
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Units

/-!
# Unramified characters from rational norm characters

This construction takes an indexed family of positive characters. For the
Waldspurger specialization that family must consist of the absolute values of
all rational algebraic characters. No algebraic-group realization or torus
structure is supplied by this module.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uG uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {I : Type uI}

/-- The common norm-one subgroup; in the rational-character specialization this
is Waldspurger's `G¹`. -/
def commonNormKernel (ν : I → (G →* ℝ≥0ˣ)) : Subgroup G :=
  ⨅ i, (ν i).ker

omit [TopologicalSpace G] in
@[simp]
theorem mem_commonNormKernel (ν : I → (G →* ℝ≥0ˣ)) (g : G) :
    g ∈ commonNormKernel ν ↔ ∀ i, ν i g = 1 := by
  simp [commonNormKernel]

instance commonNormKernel_normal (ν : I → (G →* ℝ≥0ˣ)) :
    (commonNormKernel ν).Normal :=
  Subgroup.normal_iInf_normal fun _ => inferInstance

/-- Continuous complex characters trivial on the actual common norm kernel.
This is the character group of the quotient, with its quotient topology. -/
def unramifiedCharacters (ν : I → (G →* ℝ≥0ˣ)) : Subgroup (G →ₜ* ℂˣ) where
  carrier := {χ | commonNormKernel ν ≤ χ.toMonoidHom.ker}
  one_mem' := by intro g _; simp
  mul_mem' := by
    intro χ η hχ hη g hg
    change χ g * η g = 1
    have hχg : χ g = 1 := hχ hg
    have hηg : η g = 1 := hη hg
    rw [hχg, hηg, one_mul]
  inv_mem' := by
    intro χ hχ g hg
    change (χ g)⁻¹ = 1
    have hχg : χ g = 1 := hχ hg
    rw [hχg, inv_one]

/-- The unitary subgroup of continuous complex characters. -/
def unitaryCharacters (G : Type uG) [Group G] [TopologicalSpace G] :
    Subgroup (G →ₜ* ℂˣ) where
  carrier := {χ | ∀ g, ‖(χ g : ℂ)‖ = 1}
  one_mem' := by intro g; simp
  mul_mem' := by
    intro χ η hχ hη g
    change ‖((χ g : ℂˣ) : ℂ) * (η g : ℂ)‖ = 1
    rw [norm_mul, hχ, hη, one_mul]
  inv_mem' := by
    intro χ hχ g
    change ‖(((χ g)⁻¹ : ℂˣ) : ℂ)‖ = 1
    simpa using hχ g

/-- Waldspurger's `Im X(G)` after specialization to rational norm characters.
No complex algebraic or compact Lie group structure is asserted here. -/
def unitaryUnramifiedCharacters (ν : I → (G →* ℝ≥0ˣ)) :
    Subgroup (G →ₜ* ℂˣ) :=
  unramifiedCharacters ν ⊓ unitaryCharacters G

/-- The continuous quotient projection as a group homomorphism. -/
def commonNormQuotientMap (ν : I → (G →* ℝ≥0ˣ)) :
    G →ₜ* (G ⧸ commonNormKernel ν) where
  toMonoidHom := QuotientGroup.mk' (commonNormKernel ν)
  continuous_toFun := QuotientGroup.continuous_mk

/-- Pullback of a quotient character, with its proved kernel condition. -/
def quotientCharacterPullback (ν : I → (G →* ℝ≥0ˣ))
    (χ : (G ⧸ commonNormKernel ν) →ₜ* ℂˣ) : unramifiedCharacters ν :=
  ⟨χ.comp (commonNormQuotientMap ν), by
    intro g hg
    change χ (QuotientGroup.mk g) = 1
    rw [(QuotientGroup.eq_one_iff g).mpr hg, map_one]⟩

/-- Descent to the quotient; continuity follows from the quotient topology. -/
def unramifiedCharacterDescend (ν : I → (G →* ℝ≥0ˣ))
    (χ : unramifiedCharacters ν) : (G ⧸ commonNormKernel ν) →ₜ* ℂˣ where
  toMonoidHom := QuotientGroup.lift (commonNormKernel ν) χ.val.toMonoidHom χ.property
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (commonNormKernel ν)).continuous_iff.mpr
    exact χ.val.continuous

@[simp]
theorem unramifiedCharacterDescend_mk (ν : I → (G →* ℝ≥0ˣ))
    (χ : unramifiedCharacters ν) (g : G) :
    unramifiedCharacterDescend ν χ (QuotientGroup.mk g) = χ.val g := rfl

/-- The constructed group is exactly the continuous character group of the
quotient by the common kernel. -/
def quotientCharacterEquiv (ν : I → (G →* ℝ≥0ˣ)) :
    ((G ⧸ commonNormKernel ν) →ₜ* ℂˣ) ≃* unramifiedCharacters ν where
  toFun := quotientCharacterPullback ν
  invFun := unramifiedCharacterDescend ν
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro q
    induction q using Quotient.inductionOn
    rfl
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    rfl
  map_mul' χ η := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    rfl

/-- Under an open-subgroup identity basis, every constructed character is smooth.
This uses the published continuous-complex-character open-kernel theorem. -/
theorem unramifiedCharacter_isOpen_ker [NonarchimedeanGroup G]
    (ν : I → (G →* ℝ≥0ˣ)) (χ : unramifiedCharacters ν) :
    IsOpen (χ.val.toMonoidHom.ker : Set G) :=
  Langlands.isOpen_ker_of_continuous_complex_character χ.val.toMonoidHom χ.val.continuous

end Langlands.Plancherel
