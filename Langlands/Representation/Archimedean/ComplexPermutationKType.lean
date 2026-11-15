import Langlands.Representation.Archimedean.ComplexPermutationEndomorphism
import Langlands.Representation.Archimedean.ComplexDuality.Pairing

/-!
# `U(n)`-equivariant maps between complex principal series

For the `U(n)`-finite functions `X(ds)` of the standard module of a list `ds` of complex
characters, with right translation `complexStandardRep n ds` of `U(n)`:

* evaluation at `1` separates vectors along `U(n)`-orbits (`kFiniteEval_one_separating`), since a
  function of the principal series vanishing on `U(n)` vanishes;
* `unitaryForm n ds`, `⟨f, h⟩ = ∫_{U(n)} f(k) conj(h(k)) dk`, is a `U(n)`-invariant positive
  definite sesquilinear form on `X(ds)`.

With `ComplexPermutationEndomorphism` this gives the two upgrade lemmas used for permutation
invariance, for lists `ds`, `es` between whose standard modules there are injective
`U(n)`-equivariant maps in both directions:

* `surjective_of_injective_of_kMap`: an injective `U(n)`-equivariant map `X(ds) → X(es)` is
  surjective;
* `injective_of_surjective_of_kMaps`: a surjective `U(n)`-equivariant map `X(es) → X(ds)` is
  injective.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate
open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexPermutation

open Langlands.LocalFactor.Archimedean Langlands.Archimedean.ComplexDuality

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The `U(n)`-finite functions of the standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List ComplexCharacterData) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

/-- An element of the subgroup `unitaryCompact ℂ n` as a unitary matrix. -/
def toUnitary (k : unitaryCompact ℂ n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩

theorem toUnits_toUnitary (k : unitaryCompact ℂ n) :
    (Unitary.toUnits (toUnitary k) : Langlands.GeneralLinear n ℂ) =
      (k : Langlands.GeneralLinear n ℂ) :=
  Units.ext rfl

theorem toUnits_mem_unitaryCompact (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) ∈ unitaryCompact ℂ n :=
  k.2

/-- The value of a right translate. -/
theorem complexStandardRep_apply_apply (ds : List ComplexCharacterData)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds) (g : Langlands.GeneralLinear n ℂ) :
    ((complexStandardRep n ds k f : KF n ds) : Langlands.GeneralLinear n ℂ → ℂ) g =
      (f : Langlands.GeneralLinear n ℂ → ℂ) (g * Unitary.toUnits k) :=
  rfl

/-- **Evaluation at `1` separates `U(n)`-orbits.** If `(ρ(k) f)(1) = f(k)` vanishes for every
`k ∈ U(n)`, then `f = 0`, by the Iwasawa decomposition `GL_n(ℂ) = B · U(n)`. -/
theorem kFiniteEval_one_separating (ds : List ComplexCharacterData) (f : KF n ds)
    (h : ∀ k : Matrix.unitaryGroup (Fin n) ℂ,
      kFiniteEval (complexStandardModule n ds) 1 (complexStandardRep n ds k f) = 0) :
    f = 0 := by
  apply Subtype.ext
  refine eq_zero_of_mem_principalSeries_of_eqOn f.2.1 fun k hk => ?_
  have h1 := h ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), hk⟩
  rw [kFiniteEval_apply, complexStandardRep_apply_apply, one_mul] at h1
  rw [← h1]
  exact congrArg _ (Units.ext rfl)

/-- Every vector of `X(ds)` is a finite vector for `U(n)`. -/
theorem isFiniteVector_complexStandardRep (ds : List ComplexCharacterData) (f : KF n ds) :
    FiniteVectors.IsFiniteVector (complexStandardRep n ds) f :=
  (isComplexGKModule_complexStandardModule n ds).1 f

/-! ## The invariant form -/

theorem integrable_mul_conj (ds : List ComplexCharacterData) (f h : KF n ds) :
    Integrable (fun k : unitaryCompact ℂ n =>
      (f : Langlands.GeneralLinear n ℂ → ℂ) k * conj ((h : Langlands.GeneralLinear n ℂ → ℂ) k))
      (unitaryHaar n) := by
  have hf : Continuous (f : Langlands.GeneralLinear n ℂ → ℂ) :=
    continuous_of_mem_kFiniteFunctions f.2
  have hh : Continuous fun g => conj ((h : Langlands.GeneralLinear n ℂ → ℂ) g) :=
    Complex.continuous_conj.comp (continuous_of_mem_kFiniteFunctions h.2)
  exact integrable_unitaryHaar ((hf.comp continuous_subtype_val).mul (hh.comp continuous_subtype_val))

/-- The `U(n)`-invariant sesquilinear form `⟨f, h⟩ = ∫_{U(n)} f(k) conj(h(k)) dk`. -/
def unitaryForm (n : ℕ) (ds : List ComplexCharacterData) :
    (KF n ds) →ₗ[ℂ] (KF n ds) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f h => ∫ k : unitaryCompact ℂ n,
      (f : Langlands.GeneralLinear n ℂ → ℂ) k * conj ((h : Langlands.GeneralLinear n ℂ → ℂ) k)
        ∂unitaryHaar n)
    (fun f₁ f₂ h => by
      rw [← integral_add (integrable_mul_conj ds f₁ h) (integrable_mul_conj ds f₂ h)]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c f h => by
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun f h₁ h₂ => by
      rw [← integral_add (integrable_mul_conj ds f h₁) (integrable_mul_conj ds f h₂)]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add])
    (fun c f h => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring)

theorem unitaryForm_apply (ds : List ComplexCharacterData) (f h : KF n ds) :
    unitaryForm n ds f h = ∫ k : unitaryCompact ℂ n,
      (f : Langlands.GeneralLinear n ℂ → ℂ) k * conj ((h : Langlands.GeneralLinear n ℂ → ℂ) k)
        ∂unitaryHaar n :=
  rfl

/-- The form is invariant under right translation by `U(n)` (right invariance of the Haar
measure of the compact group `U(n)`). -/
theorem unitaryForm_invariant (ds : List ComplexCharacterData)
    (g : Matrix.unitaryGroup (Fin n) ℂ) (f h : KF n ds) :
    unitaryForm n ds (complexStandardRep n ds g f) (complexStandardRep n ds g h) =
      unitaryForm n ds f h := by
  rw [unitaryForm_apply, unitaryForm_apply]
  exact integral_mul_right_eq_self (μ := unitaryHaar n)
    (fun x : unitaryCompact ℂ n => (f : Langlands.GeneralLinear n ℂ → ℂ) x *
      conj ((h : Langlands.GeneralLinear n ℂ → ℂ) x))
    (⟨Unitary.toUnits g, toUnits_mem_unitaryCompact g⟩ : unitaryCompact ℂ n)

/-- The form is positive definite: `⟨f, f⟩ = ∫ |f|²` vanishes only if `f` vanishes on `U(n)`,
hence everywhere. -/
theorem unitaryForm_self_eq_zero (ds : List ComplexCharacterData) (f : KF n ds)
    (h : unitaryForm n ds f f = 0) : f = 0 := by
  set F : Langlands.GeneralLinear n ℂ → ℂ := (f : Langlands.GeneralLinear n ℂ → ℂ) with hF
  have hc : Continuous F := continuous_of_mem_kFiniteFunctions f.2
  have hre : ∀ k : unitaryCompact ℂ n, F k * conj (F k) = ((‖F k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [unitaryForm_apply] at h
  simp_rw [← hF, hre] at h
  rw [integral_complex_ofReal] at h
  have h0 : ∫ k : unitaryCompact ℂ n, ‖F k‖ ^ 2 ∂unitaryHaar n = 0 := by
    exact_mod_cast h
  apply Subtype.ext
  refine eq_zero_of_mem_principalSeries_of_eqOn f.2.1 fun k hk => ?_
  by_contra hne
  have hpos := integral_unitaryHaar_pos (n := n)
    (f := fun k : unitaryCompact ℂ n => ‖F k‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) (fun _ => by positivity)
    (k := ⟨k, hk⟩) (by
      change ‖F k‖ ^ 2 ≠ 0
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  linarith

/-! ## Upgrading equivariant maps -/

/-- An injective `U(n)`-equivariant endomorphism of `X(es)` is surjective. -/
theorem surjective_of_injective_endo (es : List ComplexCharacterData) (E : (KF n es) →ₗ[ℂ] (KF n es))
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      E (complexStandardRep n es k f) = complexStandardRep n es k (E f))
    (hinj : Function.Injective E) : Function.Surjective E :=
  surjective_of_injective (kFiniteEval (complexStandardModule n es) 1)
    (kFiniteEval_one_separating es) (isFiniteVector_complexStandardRep es) E hE hinj

/-- A surjective `U(n)`-equivariant endomorphism of `X(es)` is injective. -/
theorem injective_of_surjective_endo (es : List ComplexCharacterData)
    (E : (KF n es) →ₗ[ℂ] (KF n es))
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      E (complexStandardRep n es k f) = complexStandardRep n es k (E f))
    (hsurj : Function.Surjective E) : Function.Injective E :=
  injective_of_surjective (kFiniteEval (complexStandardModule n es) 1)
    (kFiniteEval_one_separating es) (isFiniteVector_complexStandardRep es) (unitaryForm n es)
    (unitaryForm_invariant es) (unitaryForm_self_eq_zero es) E hE hsurj

/-- **Injective implies surjective.** If there is an injective `U(n)`-equivariant map
`Φ : X(es) → X(ds)`, then every injective `U(n)`-equivariant map `S : X(ds) → X(es)` is
surjective: `S ∘ Φ` is an injective equivariant endomorphism of `X(es)`. -/
theorem surjective_of_injective_of_kMap (ds es : List ComplexCharacterData)
    (S : (KF n ds) →ₗ[ℂ] (KF n es))
    (hS : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds),
      S (complexStandardRep n ds k f) = complexStandardRep n es k (S f))
    (hSinj : Function.Injective S) (Φ : (KF n es) →ₗ[ℂ] (KF n ds))
    (hΦ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      Φ (complexStandardRep n es k f) = complexStandardRep n ds k (Φ f))
    (hΦinj : Function.Injective Φ) : Function.Surjective S := by
  have h := surjective_of_injective_endo es (S ∘ₗ Φ)
    (fun k f => by rw [LinearMap.comp_apply, hΦ, hS, LinearMap.comp_apply])
    (hSinj.comp hΦinj)
  intro f
  obtain ⟨g, hg⟩ := h f
  exact ⟨Φ g, hg⟩

/-- **Surjective implies injective.** If there are injective `U(n)`-equivariant maps
`Φ₁ : X(ds) → X(es)` and `Φ₂ : X(es) → X(ds)`, then every surjective `U(n)`-equivariant map
`S : X(es) → X(ds)` is injective: `Φ₁ ∘ Φ₂` is injective, hence surjective, so `Φ₁` is
surjective, and `Φ₁ ∘ S` is a surjective equivariant endomorphism of `X(es)`. -/
theorem injective_of_surjective_of_kMaps (ds es : List ComplexCharacterData)
    (S : (KF n es) →ₗ[ℂ] (KF n ds))
    (hS : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      S (complexStandardRep n es k f) = complexStandardRep n ds k (S f))
    (hSsurj : Function.Surjective S) (Φ₁ : (KF n ds) →ₗ[ℂ] (KF n es))
    (hΦ₁ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds),
      Φ₁ (complexStandardRep n ds k f) = complexStandardRep n es k (Φ₁ f))
    (hΦ₁inj : Function.Injective Φ₁) (Φ₂ : (KF n es) →ₗ[ℂ] (KF n ds))
    (hΦ₂ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      Φ₂ (complexStandardRep n es k f) = complexStandardRep n ds k (Φ₂ f))
    (hΦ₂inj : Function.Injective Φ₂) : Function.Injective S := by
  have hΦ₁surj : Function.Surjective Φ₁ :=
    surjective_of_injective_of_kMap ds es Φ₁ hΦ₁ hΦ₁inj Φ₂ hΦ₂ hΦ₂inj
  have h := injective_of_surjective_endo es (Φ₁ ∘ₗ S)
    (fun k f => by rw [LinearMap.comp_apply, hS, hΦ₁, LinearMap.comp_apply])
    (hΦ₁surj.comp hSsurj)
  intro a b hab
  apply h
  simp only [LinearMap.comp_apply, hab]

end Langlands.Archimedean.ComplexPermutation
