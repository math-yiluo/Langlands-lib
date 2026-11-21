import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.Archimedean.SmoothCompactAdmissibility

/-! # Admissibility of the compact-finite genuine smooth representation -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable (F : Type) [RCLike F] (n : ℕ)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Kc" => unitaryCompact F n
local notation "D" => DerivativeSmoothVectors (matrixModel F n) R
local notation "V" => smoothKFinite F n R

/-- The matrix of a group element in the unitary compact subgroup, as a unitary matrix. -/
def unitaryCompactMatrix : Kc →* K where
  toFun k := ⟨(k.val : Matrix (Fin n) (Fin n) F), k.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem toUnits_unitaryCompactMatrix (k : Kc) :
    (Unitary.toUnits (unitaryCompactMatrix F n k) : Langlands.GeneralLinear n F) = k.val :=
  Units.ext rfl

theorem unitaryCompactMatrix_surjective : Function.Surjective (unitaryCompactMatrix F n) :=
  fun k => ⟨⟨Unitary.toUnits k, k.prop⟩, rfl⟩

theorem continuous_unitaryCompactMatrix : Continuous (unitaryCompactMatrix F n) :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

/-- The compact action on the finite-vector submodule of the genuine smooth representation. -/
def smoothKFiniteRepresentation : Representation ℂ K V :=
  FiniteVectors.representation ((DerivativeSmoothVectors.representation (matrixModel F n) R).comp
    Unitary.toUnits)

@[simp]
theorem coe_smoothKFiniteRepresentation (k : K) (v : V) :
    ((smoothKFiniteRepresentation F n R k v : V) : D) =
      DerivativeSmoothVectors.representation (matrixModel F n) R (Unitary.toUnits k) (v : D) := rfl

/-- The actual compact-finite action is admissible when the genuine smooth action is. -/
theorem isAdmissibleGKModule_smoothKFinite_of_smooth
    (hR : DerivativeSmoothVectors.IsAdmissible (matrixModel F n) R Kc) :
    IsAdmissibleGKModule (smoothKFiniteRepresentation F n R) := by
  intro d τ hτ
  let Q := DerivativeSmoothVectors.smoothIntertwiners (matrixModel F n) R Kc d
    (τ.comp (unitaryCompactMatrix F n))
  let P := gkIntertwiners (smoothKFiniteRepresentation F n R) d τ
  let T := (V).subtype
  let g : P →ₗ[ℂ] Q :=
    LinearMap.codRestrict Q ((LinearMap.llcomp ℂ _ _ _ T).comp P.subtype) fun f => by
      intro k x
      have hf := f.property (unitaryCompactMatrix F n k) x
      change T (f.val (τ (unitaryCompactMatrix F n k) *ᵥ x)) =
        DerivativeSmoothVectors.representation (matrixModel F n) R k.val (T (f.val x))
      rw [hf]
      change DerivativeSmoothVectors.representation (matrixModel F n) R
        (Unitary.toUnits (unitaryCompactMatrix F n k)) (T (f.val x)) = _
      rw [toUnits_unitaryCompactMatrix]
  let : FiniteDimensional ℂ Q := hR d _ (hτ.comp (continuous_unitaryCompactMatrix F n))
  let : IsNoetherian ℂ Q := isNoetherian_of_isNoetherianRing_of_finite ℂ Q
  have hg : Function.Injective g := by
    intro f f' h
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact Subtype.val_injective (congrArg (fun q : Q => q.val x) h)
  exact Module.Finite.of_injective g hg

/-- Genuine compact-finite vectors inherit admissibility from the norm representation. -/
theorem isAdmissibleGKModule_smoothKFinite (hR : IsAdmissible R Kc) :
    IsAdmissibleGKModule (smoothKFiniteRepresentation F n R) :=
  isAdmissibleGKModule_smoothKFinite_of_smooth F n R
    (DerivativeSmoothVectors.isAdmissible_of_norm (matrixModel F n) R Kc hR)

end Langlands.Archimedean
