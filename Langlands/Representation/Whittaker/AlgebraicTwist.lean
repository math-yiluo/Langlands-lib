import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Twist.SmoothProof

/-!
# Character twists of actual Whittaker coefficient models

This module consumes the published scalar twist. A character trivial on the
subgroup leaves the functional condition unchanged and multiplies each
coefficient by that character. No matrix-group or analytic import is needed.
-/

noncomputable section

namespace Langlands.Whittaker

universe uR uG uV

section Algebraic

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]
variable (N : Subgroup G) (θ : N →* Rˣ)
variable (χ : G →* Rˣ) (hχ : ∀ u : N, χ u.val = 1)

/-- Multiplication by the actual character on scalar-valued functions. -/
def twistFunction : (G → R) ≃ₗ[R] (G → R) where
  toFun f g := (χ g : R) * f g
  invFun f g := ((χ g)⁻¹ : Rˣ) * f g
  left_inv f := by
    funext g
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv f := by
    funext g
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' a f := by
    funext x
    exact mul_left_comm _ _ _

include hχ in
/-- Triviality on the actual subgroup preserves its character equivariance. -/
theorem twistFunction_mem {f : G → R}
    (hf : f ∈ (equivariantFunctions N θ).toSubmodule) :
    twistFunction χ f ∈ (equivariantFunctions N θ).toSubmodule := by
  intro u g
  change (χ (u.val * g) : R) * f (u.val * g) = _
  rw [map_mul, hχ u, one_mul, hf]
  exact mul_left_comm _ _ _

include hχ in
/-- The inverse multiplier also preserves the same equivariant function space. -/
theorem twistFunction_symm_mem {f : G → R}
    (hf : f ∈ (equivariantFunctions N θ).toSubmodule) :
    (twistFunction χ).symm f ∈ (equivariantFunctions N θ).toSubmodule := by
  intro u g
  change (((χ (u.val * g))⁻¹ : Rˣ) : R) * f (u.val * g) = _
  rw [map_mul, hχ u, one_mul, hf]
  exact mul_left_comm _ _ _

/-- Restrict character multiplication to the actual equivariant functions. -/
def twistFunctionEquiv :
    (equivariantFunctions N θ).toSubmodule ≃ₗ[R]
      (equivariantFunctions N θ).toSubmodule where
  toFun f := ⟨twistFunction χ f.val, twistFunction_mem N θ χ hχ f.property⟩
  invFun f := ⟨(twistFunction χ).symm f.val,
    twistFunction_symm_mem N θ χ hχ f.property⟩
  left_inv f := Subtype.ext ((twistFunction χ).left_inv f.val)
  right_inv f := Subtype.ext ((twistFunction χ).right_inv f.val)
  map_add' f g := Subtype.ext ((twistFunction χ).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((twistFunction χ).map_smul a f.val)

variable (π : Representation R G V)

/-- The same linear functional is equivariant for the twisted representation. -/
def twistFunctional (ℓ : functionals N θ π) :
    functionals N θ (Langlands.twist χ π) :=
  ⟨ℓ.val, by
    intro u v
    change ℓ.val ((χ u.val : R) • π u.val v) = _
    rw [hχ u, Units.val_one, one_smul]
    exact ℓ.property u v⟩

/-- The same functional also cancels the twist. -/
def untwistFunctional (ℓ : functionals N θ (Langlands.twist χ π)) :
    functionals N θ π :=
  ⟨ℓ.val, by
    intro u v
    have h := ℓ.property u v
    change ℓ.val ((χ u.val : R) • π u.val v) = _ at h
    simpa only [hχ u, Units.val_one, one_smul] using h⟩

/-- An actual linear equivalence of the functional spaces, retaining the map. -/
def twistFunctionalEquiv :
    functionals N θ π ≃ₗ[R] functionals N θ (Langlands.twist χ π) where
  toFun := twistFunctional N θ χ hχ π
  invFun := untwistFunctional N θ χ hχ π
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem twistFunctional_val (ℓ : functionals N θ π) :
    (twistFunctional N θ χ hχ π ℓ).val = ℓ.val := rfl

/-- In particular the construction preserves nonzero functionals. -/
theorem twistFunctional_nonzero (ℓ : functionals N θ π) (hℓ : ℓ.val ≠ 0) :
    (twistFunctional N θ χ hχ π ℓ).val ≠ 0 := hℓ

/-- Character multiplication gives exactly the coefficient of the twisted action. -/
theorem twistFunction_coefficient (ℓ : functionals N θ π) (v : V) :
    twistFunction χ (coefficientMap π ℓ v).val =
      (coefficientMap (Langlands.twist χ π)
        (twistFunctional N θ χ hχ π ℓ) v).val := by
  funext g
  change (χ g : R) * ℓ.val (π g v) = ℓ.val ((χ g : R) • π g v)
  exact (ℓ.val.map_smul _ _).symm

/-- Restrict the multiplier to the actual coefficient images. -/
def twistModelLinearMap (ℓ : functionals N θ π) :
    (coefficientModel π ℓ).toSubmodule →ₗ[R]
      (coefficientModel (Langlands.twist χ π)
        (twistFunctional N θ χ hχ π ℓ)).toSubmodule where
  toFun f :=
    ⟨twistFunctionEquiv N θ χ hχ f.val, by
      obtain ⟨v, hv⟩ := f.property
      refine ⟨v, ?_⟩
      apply Subtype.ext
      change (coefficientMap (Langlands.twist χ π)
        (twistFunctional N θ χ hχ π ℓ) v).val = twistFunction χ f.val.val
      rw [← hv]
      exact (twistFunction_coefficient N θ χ hχ π ℓ v).symm⟩
  map_add' f g := Subtype.ext ((twistFunctionEquiv N θ χ hχ).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((twistFunctionEquiv N θ χ hχ).map_smul a f.val)

theorem twistModelLinearMap_injective (ℓ : functionals N θ π) :
    Function.Injective (twistModelLinearMap N θ χ hχ π ℓ) := by
  intro f g hfg
  apply Subtype.ext
  exact (twistFunctionEquiv N θ χ hχ).injective (congrArg Subtype.val hfg)

theorem twistModelLinearMap_surjective (ℓ : functionals N θ π) :
    Function.Surjective (twistModelLinearMap N θ χ hχ π ℓ) := by
  intro f
  obtain ⟨v, hv⟩ := f.property
  refine ⟨modelMap π ℓ v, ?_⟩
  apply Subtype.ext
  calc
    (twistModelLinearMap N θ χ hχ π ℓ (modelMap π ℓ v)).val =
        coefficientMap (Langlands.twist χ π) (twistFunctional N θ χ hχ π ℓ) v := by
      apply Subtype.ext
      exact twistFunction_coefficient N θ χ hχ π ℓ v
    _ = f.val := hv

/-- The multiplier intertwines the scalar-twisted source action with the
ordinary right action on the coefficient model of the twisted representation. -/
def twistModelIntertwiner (ℓ : functionals N θ π) :
    (Langlands.twist χ
      (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)).IntertwiningMap
        (modelRepresentation (Langlands.twist χ π) (twistFunctional N θ χ hχ π ℓ)) where
  toLinearMap := twistModelLinearMap N θ χ hχ π ℓ
  isIntertwining' s := by
    ext f g
    change (χ g : R) * ((χ s : R) * f.val.val (g * s)) =
      (χ (g * s) : R) * f.val.val (g * s)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The actual coefficient model of a twist is the twist of the original model. -/
def twistModelEquiv (ℓ : functionals N θ π) :
    (Langlands.twist χ
      (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)).Equiv
        (modelRepresentation (Langlands.twist χ π) (twistFunctional N θ χ hχ π ℓ)) :=
  (twistModelIntertwiner N θ χ hχ π ℓ).ofBijective
    ⟨twistModelLinearMap_injective N θ χ hχ π ℓ,
      twistModelLinearMap_surjective N θ χ hχ π ℓ⟩

/-- An open-kernel twist has a smooth actual coefficient model when the input is smooth. -/
theorem twistModel_isSmooth [TopologicalSpace G]
    (hopen : IsOpen (χ.ker : Set G)) (hπ : IsSmooth π) (ℓ : functionals N θ π) :
    IsSmooth
      (V := (coefficientModel (Langlands.twist χ π)
        (twistFunctional N θ χ hχ π ℓ)).toSubmodule)
      (modelRepresentation (Langlands.twist χ π) (twistFunctional N θ χ hχ π ℓ)) :=
  model_isSmooth (Langlands.twist χ π)
    ((isSmooth_twist_iff χ π hopen).mpr hπ) _

end Algebraic

end Langlands.Whittaker
