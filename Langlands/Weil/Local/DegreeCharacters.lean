import Langlands.Weil.Pullback
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Characters obtained from the integer degree

The degree group has its discrete topology; complex numbers have their usual topology.
The norm convention is geometric degree `+1` with value `q⁻¹`.
Actual local residue and Galois data are specialized in a separate assembly module.
-/

namespace Langlands.Weil.Local

universe u v

/-- The continuous character of the discrete integers with value `z` at `+1`. -/
noncomputable def degreePowers (z : ℂˣ) : Degree →ₜ* ℂˣ where
  toMonoidHom := zpowersHom ℂˣ z
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem degreePowers_apply (z : ℂˣ) (n : Degree) :
    degreePowers z n = z ^ n.toAdd := rfl

variable {W : Type u} [Group W] [TopologicalSpace W]

/-- Pull back an integer character along a continuous degree. -/
noncomputable def unramifiedCharacter (d : W →ₜ* Degree) (z : ℂˣ) : W →ₜ* ℂˣ :=
  (degreePowers z).comp d

@[simp] theorem unramifiedCharacter_apply (d : W →ₜ* Degree) (z : ℂˣ) (w : W) :
    unramifiedCharacter d z w = z ^ (d w).toAdd := rfl

/-- Every constructed character is trivial on degree-zero inertia. -/
theorem unramifiedCharacter_on_kernel (d : W →ₜ* Degree) (z : ℂˣ)
    {w : W} (hw : w ∈ d.toMonoidHom.ker) : unramifiedCharacter d z w = 1 := by
  change d w = 1 at hw
  simp [hw]

/-- Evaluation at any geometric degree-one lift, without choosing a lift. -/
theorem unramifiedCharacter_degree_one (d : W →ₜ* Degree) (z : ℂˣ)
    {w : W} (hw : d w = Multiplicative.ofAdd (1 : ℤ)) :
    unramifiedCharacter d z w = z := by
  simp [hw]

/-- Dependence on the value at geometric degree one is multiplicative. -/
noncomputable def unramifiedCharacterHom (d : W →ₜ* Degree) :
    ℂˣ →* (W →ₜ* ℂˣ) where
  toFun := unramifiedCharacter d
  map_one' := by ext w; simp
  map_mul' z z' := by ext w; simp [mul_zpow]

@[simp] theorem unramifiedCharacter_comp
    {W' : Type v} [Group W'] [TopologicalSpace W']
    (d : W →ₜ* Degree) (f : W' →ₜ* W) (z : ℂˣ) :
    (unramifiedCharacter d z).comp f = unramifiedCharacter (d.comp f) z := rfl

/-- A positive natural cardinality, as a nonzero complex number. -/
noncomputable def cardinalityUnit (q : ℕ) (hq : 0 < q) : ℂˣ :=
  Units.mk0 (q : ℂ) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))

@[simp] theorem cardinalityUnit_val (q : ℕ) (hq : 0 < q) :
    (cardinalityUnit q hq : ℂ) = (q : ℂ) := rfl

/-- The degree-normalized norm character, with value `q⁻¹` at geometric degree one. -/
noncomputable def normCharacter (d : W →ₜ* Degree) (q : ℕ) (hq : 0 < q) :
    W →ₜ* ℂˣ := unramifiedCharacter d (cardinalityUnit q hq)⁻¹

theorem normCharacter_apply (d : W →ₜ* Degree) (q : ℕ) (hq : 0 < q) (w : W) :
    (normCharacter d q hq w : ℂ) = (q : ℂ) ^ (-(d w).toAdd) := by
  simp [normCharacter, zpow_neg]

theorem normCharacter_on_kernel (d : W →ₜ* Degree) (q : ℕ) (hq : 0 < q)
    {w : W} (hw : w ∈ d.toMonoidHom.ker) : normCharacter d q hq w = 1 :=
  unramifiedCharacter_on_kernel d _ hw

theorem normCharacter_degree_one (d : W →ₜ* Degree) (q : ℕ) (hq : 0 < q)
    {w : W} (hw : d w = Multiplicative.ofAdd (1 : ℤ)) :
    (normCharacter d q hq w : ℂ) = (q : ℂ)⁻¹ := by
  simp [normCharacter_apply, hw]

theorem normCharacter_degree_neg_one (d : W →ₜ* Degree) (q : ℕ) (hq : 0 < q)
    {w : W} (hw : d w = Multiplicative.ofAdd (-1 : ℤ)) :
    (normCharacter d q hq w : ℂ) = (q : ℂ) := by
  simp [normCharacter_apply, hw]

@[simp] theorem normCharacter_comp
    {W' : Type v} [Group W'] [TopologicalSpace W']
    (d : W →ₜ* Degree) (f : W' →ₜ* W) (q : ℕ) (hq : 0 < q) :
    (normCharacter d q hq).comp f = normCharacter (d.comp f) q hq := rfl

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- Unramified characters on the existing generic Weil pullback. -/
noncomputable abbrev pullbackCharacter (φ : Γ →ₜ* ProfiniteIntegers) (z : ℂˣ) :
    Pullback φ →ₜ* ℂˣ := unramifiedCharacter (degree φ) z

/-- The norm character on the existing generic Weil pullback. -/
noncomputable abbrev pullbackNormCharacter (φ : Γ →ₜ* ProfiniteIntegers)
    (q : ℕ) (hq : 0 < q) : Pullback φ →ₜ* ℂˣ := normCharacter (degree φ) q hq

@[simp] theorem pullbackCharacter_inertiaInclusion
    (φ : Γ →ₜ* ProfiniteIntegers) (z : ℂˣ) (i : inertia φ) :
    pullbackCharacter φ z (inertiaInclusion φ i) = 1 := by
  change z ^ (0 : ℤ) = 1
  exact zpow_zero z

@[simp] theorem pullbackNormCharacter_inertiaInclusion
    (φ : Γ →ₜ* ProfiniteIntegers) (q : ℕ) (hq : 0 < q) (i : inertia φ) :
    pullbackNormCharacter φ q hq (inertiaInclusion φ i) = 1 :=
  pullbackCharacter_inertiaInclusion φ _ i

end Langlands.Weil.Local
