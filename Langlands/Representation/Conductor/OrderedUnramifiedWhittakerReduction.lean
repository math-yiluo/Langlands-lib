import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerStatement
import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Representation.ScalarSubReduction
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Group.GL.LocalFieldUpperUnipotentCompactSubgroup

/-!
# The normalized inverse Whittaker realization from three representation-theoretic inputs

For the unramified principal series `I(z)` over a nonarchimedean local field, the
conclusion of `OrderedUnramifiedWhittakerRealizationStatement` follows from:

* the inverse-character coinvariants of `I(z)` are a line;
* every nonzero subrepresentation of `I(z)` has nonzero inverse-character coinvariants;
* every inverse-character functional `ℓ` maps the spherical section `f₀` to
  `ℓ(f₀)` times the explicit spherical Whittaker function.

The proof is purely algebraic apart from the extension of functionals along the inclusion
of a subrepresentation, which uses exactness of character coinvariants.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedWhittakerReduction

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF

attribute [local instance] LocalFieldTopology.upperUnipotent_nonarchimedean

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ) {q : ℕ}
  (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
  (ψ : UnitaryAdditiveCharacter F)

/-- The inverse-character coinvariants of a representation of `GL_(n+1)(F)`. -/
abbrev InverseCoinvariants {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :=
  Jacquet.Localization.Coinvariants π (upperUnipotent (n + 1) F) (inverseStandardCharacter ψ n)

/-- If the inverse-character coinvariants are a line, the inverse-character functionals
form a line. -/
theorem exists_functional_of_finrank
    (hdim : Module.finrank ℂ (InverseCoinvariants n ψ (principalSeries hϖ n hq z)) = 1) :
    ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z), ℓ ≠ 0 ∧
      ∀ ℓ' : glInverseFunctionals ψ n (principalSeries hϖ n hq z), ∃ c : ℂ, c • ℓ = ℓ' := by
  have h : Module.finrank ℂ (glInverseFunctionals ψ n (principalSeries hϖ n hq z)) = 1 := by
    rw [LinearEquiv.finrank_eq (functionalsLocalizationDualEquiv _ _ _), Subspace.dual_finrank_eq,
      hdim]
  exact finrank_eq_one_iff'.mp h

/-- Kernel argument: a functional spanning the line of inverse-character functionals has an
injective coefficient map, once nonzero subrepresentations have nonzero coinvariants. -/
theorem coefficientMap_injective
    (hnd : ∀ K : Subrepresentation (principalSeries hϖ n hq z), K ≠ ⊥ →
      Nontrivial (InverseCoinvariants n ψ K.toRepresentation))
    (ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z))
    (hspan : ∀ ℓ' : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
      ∃ c : ℂ, c • ℓ = ℓ') :
    Function.Injective (coefficientMap (principalSeries hϖ n hq z) ℓ) := by
  let K := (coefficientMap (principalSeries hϖ n hq z) ℓ).ker
  have hK : K = ⊥ := by
    by_contra hne
    have := hnd K hne
    obtain ⟨x, hx⟩ := exists_ne (0 : InverseCoinvariants n ψ K.toRepresentation)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
    set m := (functionalsLocalizationDualEquiv (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n) K.toRepresentation).symm φ
    have hm : m ≠ 0 := by
      intro h0
      apply hφ
      have : φ = functionalsLocalizationDualEquiv (upperUnipotent (n + 1) F)
          (inverseStandardCharacter ψ n) K.toRepresentation m := by
        simp [m]
      rw [this, h0, map_zero, LinearMap.zero_apply]
    obtain ⟨ℓ', hℓ'⟩ := functionalsComap_surjective_of_smooth
      (upperUnipotent (n + 1) F) (localField_upperUnipotent_isLimitOfCompactSubgroups F (n + 1))
      (inverseStandardCharacter ψ n)
      (RankinSelberg.isLocallyConstant_of_continuous_complex_character _
        (inverseStandardCharacterContinuous ψ n).continuous)
      (ScalarSubReduction.inclusion _ K) (ScalarSubReduction.inclusion_injective _ K)
      (principalSeries_smooth hϖ n hq z) m
    apply hm
    obtain ⟨c, hc⟩ := hspan ℓ'
    rw [← hℓ', ← hc]
    apply Subtype.ext
    ext v
    change c * ℓ.val (v : PrincipalSeries hϖ n hq z) = 0
    have hv : coefficientMap (principalSeries hϖ n hq z) ℓ (v : PrincipalSeries hϖ n hq z) = 0 :=
      v.property
    have h1 : ℓ.val (v : PrincipalSeries hϖ n hq z) =
        (coefficientMap (principalSeries hϖ n hq z) ℓ (v : PrincipalSeries hϖ n hq z)).val 1 := by
      change _ = ℓ.val (principalSeries hϖ n hq z 1 _)
      rw [map_one, Module.End.one_apply]
    rw [h1, hv]
    simp
  intro f f' hff'
  have hmem : f - f' ∈ K := by
    change coefficientMap (principalSeries hϖ n hq z) ℓ (f - f') = 0
    rw [map_sub, hff', sub_self]
  rw [hK] at hmem
  exact sub_eq_zero.mp hmem

/-- Assembly: from the three inputs, a rescaled spanning functional is nonzero, has an
injective coefficient map and sends the spherical section to the explicit spherical
Whittaker function. -/
theorem realization_of_inputs
    (hdim : Module.finrank ℂ (InverseCoinvariants n ψ (principalSeries hϖ n hq z)) = 1)
    (hnd : ∀ K : Subrepresentation (principalSeries hϖ n hq z), K ≠ ⊥ →
      Nontrivial (InverseCoinvariants n ψ K.toRepresentation))
    (hsph : ∀ (ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z))
      (g : Langlands.GeneralLinear (n + 1) F),
      (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
        ℓ.val (sphericalSection hϖ n hq z) *
          Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g) :
    ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
      ℓ.val ≠ 0 ∧
      Function.Injective (coefficientMap (principalSeries hϖ n hq z) ℓ) ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
          Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g := by
  obtain ⟨ℓ₀, -, hspan⟩ := exists_functional_of_finrank hϖ n hq z ψ hdim
  have hinj := coefficientMap_injective hϖ n hq z ψ hnd ℓ₀ hspan
  set f₀ := sphericalSection hϖ n hq z
  have hc : ℓ₀.val f₀ ≠ 0 := by
    intro h0
    apply sphericalSection_ne_zero hϖ n hq z
    apply hinj
    rw [map_zero]
    apply Subtype.ext
    funext g
    rw [hsph ℓ₀ g, h0, zero_mul]
    rfl
  set c : ℂ := (ℓ₀.val f₀)⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero hc
  have hcoef : ∀ (f : PrincipalSeries hϖ n hq z) (g : Langlands.GeneralLinear (n + 1) F),
      (coefficientMap (principalSeries hϖ n hq z) (c • ℓ₀) f).val g =
        c * (coefficientMap (principalSeries hϖ n hq z) ℓ₀ f).val g := fun _ _ => rfl
  refine ⟨c • ℓ₀, ?_, ?_, ?_⟩
  · intro h0
    apply hc
    have : (c • ℓ₀).val f₀ = c * ℓ₀.val f₀ := rfl
    rw [h0, LinearMap.zero_apply] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc0
  · intro f f' hff'
    apply hinj
    apply Subtype.ext
    funext g
    have h := congrArg (fun W => W.val g) hff'
    simp only [hcoef] at h
    exact mul_left_cancel₀ hc0 h
  · intro g
    rw [hcoef, hsph ℓ₀ g, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Langlands.Conductor.OrderedUnramifiedWhittakerReduction
