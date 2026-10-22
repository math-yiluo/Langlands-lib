import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.Maps
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# The Weyl--inverse-transpose transform on Whittaker functions

The matrix maps are imported from the geometry branch. The constructions here
prove character reversal and construct the coefficient model of the
inverse-transpose pullback. Identification with a contragredient is separate.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ}

/-- Weyl conjugation of inverse transpose preserves the actual unipotent subgroup. -/
def reflectedUnipotent (u : upperUnipotent (n + 1) F) :
    upperUnipotent (n + 1) F :=
  ⟨weylLong (n + 1) F * inverseTranspose (n + 1) F u.val * weylLong (n + 1) F,
    by
      constructor
      · intro i j hji
        rw [weylLong_conjugate_entry, inverseTranspose_entry]
        exact UpperUnipotent.entry_eq_zero (u⁻¹) (Fin.rev_lt_rev.mpr hji)
      · intro i
        rw [weylLong_conjugate_entry, inverseTranspose_entry]
        exact UpperUnipotent.entry_diag (u⁻¹) i.rev⟩

@[simp] theorem reflectedUnipotent_val (u : upperUnipotent (n + 1) F) :
    (reflectedUnipotent u).val =
      weylLong (n + 1) F * inverseTranspose (n + 1) F u.val * weylLong (n + 1) F := rfl

/-- Adjacent entries reverse order and change sign. -/
theorem reflectedUnipotent_adjacent (u : upperUnipotent (n + 1) F) (i : Fin n) :
    (reflectedUnipotent u).val i.castSucc i.succ =
      -u.val i.rev.castSucc i.rev.succ := by
  rw [reflectedUnipotent_val, weylLong_conjugate_entry, inverseTranspose_entry,
    Fin.rev_succ, Fin.rev_castSucc]
  exact UpperUnipotent.inv_adjacent_entry u i.rev

/-- Consequently the first-superdiagonal sum is negated. -/
theorem reflectedUnipotent_sum (u : upperUnipotent (n + 1) F) :
    (∑ i : Fin n, (reflectedUnipotent u).val i.castSucc i.succ) =
      -(∑ i : Fin n, u.val i.castSucc i.succ) := by
  simp only [reflectedUnipotent_adjacent, Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun i : Fin n => u.val i.castSucc i.succ)

variable [TopologicalSpace F]

/-- The standard character becomes the inverse character under reflection. -/
@[simp] theorem standardCharacter_reflected (ψ : UnitaryAdditiveCharacter F)
    (u : upperUnipotent (n + 1) F) :
    standardCharacter ψ n (reflectedUnipotent u) = inverseStandardCharacter ψ n u := by
  apply Units.ext
  simp only [standardCharacter_apply, reflectedUnipotent_sum,
    inverseStandardCharacter_apply, UnitaryAdditiveCharacter.complex, AddChar.map_neg_eq_inv]

@[simp] theorem inverseStandardCharacter_reflected (ψ : UnitaryAdditiveCharacter F)
    (u : upperUnipotent (n + 1) F) :
    inverseStandardCharacter ψ n (reflectedUnipotent u) = standardCharacter ψ n u := by
  change (standardCharacter ψ n (reflectedUnipotent u))⁻¹ = _
  rw [standardCharacter_reflected]
  exact inv_inv _

variable [IsTopologicalRing F]

/-- The actual Weyl--inverse-transpose argument intertwines left unipotent multiplication. -/
theorem weylInverseTranspose_left_unipotent (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    weylInverseTranspose (n + 1) F (u.val * g) =
      (reflectedUnipotent u).val * weylInverseTranspose (n + 1) F g := by
  simp only [weylInverseTranspose_apply, map_mul, reflectedUnipotent_val]
  calc
    _ = (weylLong (n + 1) F * inverseTranspose (n + 1) F u.val) *
        ((weylLong (n + 1) F * weylLong (n + 1) F) *
          inverseTranspose (n + 1) F g) := by
      rw [weylLong_mul_self, one_mul, mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- The actual function transform, as a linear involution on all complex functions. -/
def dualFunction (n : ℕ) :
    (Langlands.GeneralLinear (n + 1) F → ℂ) ≃ₗ[ℂ]
      (Langlands.GeneralLinear (n + 1) F → ℂ) where
  toFun f := f ∘ weylInverseTranspose (n + 1) F
  invFun f := f ∘ weylInverseTranspose (n + 1) F
  left_inv f := by
    funext g
    simp only [Function.comp_apply, weylInverseTranspose_involutive]
  right_inv f := by
    funext g
    simp only [Function.comp_apply, weylInverseTranspose_involutive]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dualFunction_apply (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    dualFunction n f g = f (weylLong (n + 1) F * inverseTranspose (n + 1) F g) := rfl

/-- Every standard-equivariant function transforms by the inverse character. -/
theorem dualFunction_mem (ψ : UnitaryAdditiveCharacter F)
    {f : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hf : f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule) :
    dualFunction n f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n)).toSubmodule := by
  intro u g
  change f (weylInverseTranspose (n + 1) F (u.val * g)) = _
  rw [weylInverseTranspose_left_unipotent, hf, standardCharacter_reflected]
  rfl

/-- The same transform takes inverse-equivariant functions back to standard ones. -/
theorem dualFunction_inverse_mem (ψ : UnitaryAdditiveCharacter F)
    {f : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hf : f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n)).toSubmodule) :
    dualFunction n f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule := by
  intro u g
  change f (weylInverseTranspose (n + 1) F (u.val * g)) = _
  rw [weylInverseTranspose_left_unipotent, hf, inverseStandardCharacter_reflected]
  rfl

/-- Character reversal is a linear equivalence of the actual equivariant function spaces. -/
def dualFunctionEquiv (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    (equivariantFunctions (upperUnipotent (n + 1) F) (standardCharacter ψ n)).toSubmodule
      ≃ₗ[ℂ]
    (equivariantFunctions (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n)).toSubmodule where
  toFun f := ⟨dualFunction n f.val, dualFunction_mem ψ f.property⟩
  invFun f := ⟨dualFunction n f.val, dualFunction_inverse_mem ψ f.property⟩
  left_inv f := Subtype.ext ((dualFunction n).left_inv f.val)
  right_inv f := Subtype.ext ((dualFunction n).right_inv f.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right translation is transported through the inverse-transpose group automorphism. -/
theorem dualFunction_translate (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (s : Langlands.GeneralLinear (n + 1) F) :
    dualFunction n (rightTranslation ℂ _ s f) =
      rightTranslation ℂ _ (inverseTranspose (n + 1) F s) (dualFunction n f) := by
  funext g
  change f ((weylLong (n + 1) F * inverseTranspose (n + 1) F g) * s) =
    f (weylLong (n + 1) F *
      inverseTranspose (n + 1) F (g * inverseTranspose (n + 1) F s))
  rw [map_mul, inverseTranspose_involutive, mul_assoc]

section CoefficientModels

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Pullback along the actual inverse-transpose group automorphism.
This construction is not defined to be the contragredient. -/
def inverseTransposePullback :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) V :=
  π.comp (inverseTranspose (n + 1) F).toMonoidHom

omit [TopologicalSpace F] [IsTopologicalRing F] in
@[simp] theorem inverseTransposePullback_apply
    (g : Langlands.GeneralLinear (n + 1) F) :
    inverseTransposePullback π g = π (inverseTranspose (n + 1) F g) := rfl

/-- Translation of the functional by the long Weyl representative reverses
its unipotent character for the inverse-transpose pullback. -/
def dualFunctional (ℓ : glFunctionals ψ n π) :
    glInverseFunctionals ψ n (inverseTransposePullback π) :=
  ⟨ℓ.val.comp (π (weylLong (n + 1) F)), by
    intro u v
    change ℓ.val (π (weylLong (n + 1) F)
      (π (inverseTranspose (n + 1) F u.val) v)) =
        (inverseStandardCharacter ψ n u : ℂ) * ℓ.val (π (weylLong (n + 1) F) v)
    have he : weylLong (n + 1) F * inverseTranspose (n + 1) F u.val =
        (reflectedUnipotent u).val * weylLong (n + 1) F := by
      simp only [reflectedUnipotent_val, mul_assoc, weylLong_mul_self, mul_one]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply,
      ℓ.property, standardCharacter_reflected]⟩

omit [IsTopologicalRing F] in
@[simp] theorem dualFunctional_apply (ℓ : glFunctionals ψ n π) (v : V) :
    (dualFunctional ψ π ℓ).val v = ℓ.val (π (weylLong (n + 1) F) v) := rfl

omit [IsTopologicalRing F] in
/-- The transported functional is nonzero whenever the original one is. -/
theorem dualFunctional_nonzero (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    (dualFunctional ψ π ℓ).val ≠ 0 := by
  intro hzero
  apply hℓ
  ext v
  have hv := LinearMap.congr_fun hzero (π (weylLong (n + 1) F) v)
  change ℓ.val (π (weylLong (n + 1) F) (π (weylLong (n + 1) F) v)) = 0 at hv
  rw [← Module.End.mul_apply, ← map_mul, weylLong_mul_self, map_one,
    Module.End.one_apply] at hv
  exact hv

/-- The transformed coefficient is exactly a coefficient of the constructed pullback. -/
theorem dualFunction_coefficient (ℓ : glFunctionals ψ n π) (v : V) :
    dualFunction n (coefficientMap π ℓ v).val =
      (coefficientMap (inverseTransposePullback π) (dualFunctional ψ π ℓ) v).val := by
  funext g
  change ℓ.val (π (weylLong (n + 1) F * inverseTranspose (n + 1) F g) v) =
    ℓ.val (π (weylLong (n + 1) F) (π (inverseTranspose (n + 1) F g) v))
  rw [map_mul, Module.End.mul_apply]

/-- Restrict the actual transform to the actual coefficient images. -/
def dualModelLinearMap (ℓ : glFunctionals ψ n π) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (dualFunctional ψ π ℓ)).toSubmodule where
  toFun f :=
    ⟨dualFunctionEquiv ψ n f.val, by
      obtain ⟨v, hv⟩ := f.property
      refine ⟨v, ?_⟩
      apply Subtype.ext
      change (coefficientMap (inverseTransposePullback π) (dualFunctional ψ π ℓ) v).val =
        dualFunction n f.val.val
      rw [← hv]
      exact (dualFunction_coefficient ψ π ℓ v).symm⟩
  map_add' f g := Subtype.ext ((dualFunctionEquiv ψ n).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((dualFunctionEquiv ψ n).map_smul a f.val)

theorem dualModelLinearMap_injective (ℓ : glFunctionals ψ n π) :
    Function.Injective (dualModelLinearMap ψ π ℓ) := by
  intro f g hfg
  apply Subtype.ext
  exact (dualFunctionEquiv ψ n).injective (congrArg Subtype.val hfg)

theorem dualModelLinearMap_surjective (ℓ : glFunctionals ψ n π) :
    Function.Surjective (dualModelLinearMap ψ π ℓ) := by
  intro f
  obtain ⟨v, hv⟩ := f.property
  refine ⟨modelMap π ℓ v, ?_⟩
  apply Subtype.ext
  calc
    (dualModelLinearMap ψ π ℓ (modelMap π ℓ v)).val =
        coefficientMap (inverseTransposePullback π) (dualFunctional ψ π ℓ) v := by
      apply Subtype.ext
      exact dualFunction_coefficient ψ π ℓ v
    _ = f.val := hv

/-- The source model action is pulled back through inverse transpose;
the target carries its ordinary right-translation action. -/
def dualModelIntertwiner (ℓ : glFunctionals ψ n π) :
    (inverseTransposePullback (V := (coefficientModel π ℓ).toSubmodule)
      (modelRepresentation π ℓ)).IntertwiningMap
      (modelRepresentation (inverseTransposePullback π) (dualFunctional ψ π ℓ)) where
  toLinearMap := dualModelLinearMap ψ π ℓ
  isIntertwining' s := by
    ext f g
    change f.val.val
        ((weylLong (n + 1) F * inverseTranspose (n + 1) F g) *
          inverseTranspose (n + 1) F s) =
      f.val.val (weylLong (n + 1) F * inverseTranspose (n + 1) F (g * s))
    rw [map_mul, mul_assoc]

/-- The constructed inverse-transpose coefficient model is equivalent to the
pullback of the original model. No irreducibility or uniqueness theorem is used. -/
def dualModelEquiv (ℓ : glFunctionals ψ n π) :
    (inverseTransposePullback (V := (coefficientModel π ℓ).toSubmodule)
      (modelRepresentation π ℓ)).Equiv
      (modelRepresentation (inverseTransposePullback π) (dualFunctional ψ π ℓ)) :=
  (dualModelIntertwiner ψ π ℓ).ofBijective
    ⟨dualModelLinearMap_injective ψ π ℓ, dualModelLinearMap_surjective ψ π ℓ⟩

omit [IsTopologicalRing F] in
/-- Pullback preserves smoothness: the published continuous-pullback theorem. -/
theorem inverseTransposePullback_isSmooth (hπ : IsSmooth π) :
    IsSmooth (inverseTransposePullback π) :=
  Langlands.isSmooth_comp _ (continuous_inverseTranspose (n + 1) F) hπ

omit [IsTopologicalRing F] in
/-- The actual transformed coefficient model is smooth under the same hypothesis. -/
theorem dualModel_isSmooth (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π) :
    IsSmooth
      (V := (coefficientModel (inverseTransposePullback π) (dualFunctional ψ π ℓ)).toSubmodule)
      (modelRepresentation (inverseTransposePullback π) (dualFunctional ψ π ℓ)) :=
  model_isSmooth (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ) _

end CoefficientModels

end Langlands.Whittaker
