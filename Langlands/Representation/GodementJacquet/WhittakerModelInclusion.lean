import Langlands.Representation.GodementJacquet.WhittakerAveraging
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.GodementJacquet.ModelWhittakerRationalityStatement
import Langlands.Representation.GodementJacquet.WhittakerModelComparisonStatement
import Langlands.Representation.GodementJacquet.ZetaLinear
import Langlands.LocalField.Normalization.Proof

/-!
# Matrix-coefficient integrals of the model as sums of Whittaker integrals

JPSS (1983), Section (5.2), printed 421: on an admissible coefficient model, every
smooth functional agrees with a finite combination of compact averages of
evaluations, and a conjugation change of variables turns each resulting integral
into a full-matrix Whittaker integral. Given convergence and rationality of every
Whittaker integral on the model, this gives `I₂ ⊆ I₃`.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg Topology
open scoped ENNReal NNReal BigOperators

universe uF uV uG

section Invariant

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A functional invariant under a compact open subgroup has the same value at a
smooth vector and at its average over that subgroup. -/
theorem apply_averageMap_of_invariant (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (Λ : Module.Dual ℂ V)
    (hΛ : ∀ k ∈ K, ∀ v, Λ (ρ k v) = Λ v) (v : V) :
    Λ (Compact.averageMap ρ hρ K hK v) = Λ v := by
  classical
  have := Compact.finite_orbit_of_smooth ρ hρ K hK v
  let := Fintype.ofFinite (Compact.orbit (ρ.comp K.toSubgroup.subtype) v)
  change Λ (Compact.orbitMean (ρ.comp K.toSubgroup.subtype) v) = Λ v
  rw [Compact.orbitMean_eq_finiteMean]
  unfold Compact.finiteMean
  rw [map_smul, map_sum]
  have hx : ∀ x : Compact.orbit (ρ.comp K.toSubgroup.subtype) v, Λ x.val = Λ v := by
    rintro ⟨x, k, rfl⟩
    exact hΛ k.val k.property v
  simp only [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  have hc : (Fintype.card (Compact.orbit (ρ.comp K.toSubgroup.subtype) v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- Two functionals invariant under a compact open subgroup agree once they agree
on the vectors fixed by that subgroup. -/
theorem eq_of_invariant_of_eqOn_fixedVectors (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (Λ₁ Λ₂ : Module.Dual ℂ V)
    (h₁ : ∀ k ∈ K, ∀ v, Λ₁ (ρ k v) = Λ₁ v) (h₂ : ∀ k ∈ K, ∀ v, Λ₂ (ρ k v) = Λ₂ v)
    (heq : ∀ v ∈ fixedVectors ρ K.toSubgroup, Λ₁ v = Λ₂ v) : Λ₁ = Λ₂ := by
  ext v
  rw [← apply_averageMap_of_invariant ρ hρ K hK Λ₁ h₁ v,
    ← apply_averageMap_of_invariant ρ hρ K hK Λ₂ h₂ v]
  exact heq _ (Compact.averageMap_mem_fixedVectors ρ hρ K hK v)

/-- On a finite-dimensional subspace, a functional vanishing on the common kernel
of a family of functionals is a finite combination of them. -/
theorem exists_finsupp_eqOn_of_ker {M : Type uV} [AddCommGroup M] [Module ℂ M]
    (E : Submodule ℂ M) (hE : Module.Finite ℂ E) {ι : Type*} (ev : ι → Module.Dual ℂ M)
    (Λ : Module.Dual ℂ M) (hker : ∀ e ∈ E, (∀ i, ev i e = 0) → Λ e = 0) :
    ∃ c : ι →₀ ℂ, ∀ e ∈ E, Λ e = ∑ i ∈ c.support, c i * ev i e := by
  have hk : ⨅ i, LinearMap.ker ((ev i).comp E.subtype) ≤ LinearMap.ker (Λ.comp E.subtype) := by
    intro e he
    rw [Submodule.mem_iInf] at he
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at he ⊢
    exact hker e.val e.property he
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker hk)
  refine ⟨c, fun e he => ?_⟩
  have e' := congrArg (fun φ : Module.Dual ℂ E => φ ⟨e, he⟩) hc
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.comp_apply, Submodule.subtype_apply] at e'
  exact e'.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A functional fixed by a subgroup in the algebraic dual is invariant under that
subgroup. -/
theorem apply_of_mem_fixedVectors_dual (ρ : Representation ℂ G V) (K : Subgroup G)
    {Λ : Module.Dual ℂ V} (hΛ : Λ ∈ fixedVectors ρ.dual K) {k : G} (hk : k ∈ K) (v : V) :
    Λ (ρ k v) = Λ v := by
  have e : ρ.dual k Λ = Λ := hΛ ⟨k, hk⟩
  calc Λ (ρ k v) = (ρ.dual k Λ) (ρ k v) := by rw [e]
    _ = Λ (ρ k⁻¹ (ρ k v)) := rfl
    _ = Λ v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- If the vectors fixed by a compact open subgroup form a finite-dimensional space,
an invariant functional vanishing on the common kernel there of a family of
invariant functionals is a finite combination of that family. -/
theorem exists_eq_sum_of_invariant (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hfin : Module.Finite ℂ (fixedVectors ρ K.toSubgroup)) {ι : Type*}
    (ev : ι → Module.Dual ℂ V) (hev : ∀ i, ∀ k ∈ K, ∀ v, ev i (ρ k v) = ev i v)
    (Λ : Module.Dual ℂ V) (hΛ : ∀ k ∈ K, ∀ v, Λ (ρ k v) = Λ v)
    (hker : ∀ e ∈ fixedVectors ρ K.toSubgroup, (∀ i, ev i e = 0) → Λ e = 0) :
    ∃ c : ι →₀ ℂ, ∀ v, Λ v = ∑ i ∈ c.support, c i * ev i v := by
  obtain ⟨c, hc⟩ := exists_finsupp_eqOn_of_ker _ hfin ev Λ hker
  let Λ₂ : Module.Dual ℂ V := ∑ i ∈ c.support, c i • ev i
  have hΛ₂ : ∀ v, Λ₂ v = ∑ i ∈ c.support, c i * ev i v := fun v => by
    simp only [Λ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h := eq_of_invariant_of_eqOn_fixedVectors ρ hρ K hK Λ Λ₂ hΛ
    (fun k hk v => by
      rw [hΛ₂, hΛ₂]
      exact Finset.sum_congr rfl fun i _ => by rw [hev i k hk v])
    (fun v hv => by rw [hΛ₂]; exact hc v hv)
  exact ⟨c, fun v => by rw [h, hΛ₂]⟩

omit [IsTopologicalGroup G] in
/-- A bi-smooth matrix coefficient is `g ↦ Λ(ρ(g)v)`. -/
theorem biSmoothCoefficient_apply (ρ : Representation ℂ G V) (Λ : SmoothDual ρ)
    (v : smoothVectors ρ) (g : G) : biSmoothCoefficient ρ Λ v g = Λ.val (ρ g v.val) :=
  rfl

end Invariant

section ShiftedValues

/-- A Laurent span of rational functions is closed under complex constant multiples. -/
theorem const_mul_mem_zetaSpan {values : Set RationalFunctions} (c : ℂ) {R : RationalFunctions}
    (hR : R ∈ zetaSpan values) : RatFunc.C c * R ∈ zetaSpan values := by
  have h := Submodule.smul_mem (zetaSpan values) (LaurentPolynomial.C c) hR
  simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using h

end ShiftedValues

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelInclusionTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelInclusionValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelInclusionLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance modelInclusionMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance modelInclusionBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance modelInclusionSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance modelInclusionSigmaCompact (n : ℕ) : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)

variable {n : ℕ}

section Conjugation

/-- The conjugated test function `M ↦ Φ(h⁻¹ M h)`, again Schwartz–Bruhat on all
square matrices. -/
def conjTest (Φ : MatrixTestFunction n F.Carrier)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) : MatrixTestFunction n F.Carrier :=
  let e : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier ≃ₜ
      Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier :=
    { toFun := fun M => (h⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val * M * h.val
      invFun := fun M => h.val * M * (h⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val
      left_inv := fun M => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      right_inv := fun M => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  ⟨fun M => Φ (e M), Φ.locallyConstant.comp_continuous e.continuous,
    Φ.hasCompactSupport.comp_homeomorph e⟩

@[simp] theorem conjTest_apply (Φ : MatrixTestFunction n F.Carrier)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    conjTest F Φ h M = Φ ((h⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val * M * h.val) :=
  rfl

/-- The pointwise identity behind the conjugation change of variables. -/
theorem matrixIntegrand_conj (Φ : MatrixTestFunction n F.Carrier)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) (u : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (conjTest F Φ h) s (fun y => u (y * h)) (h * g * h⁻¹) =
      Φ g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
        u (h * g) := by
  have hM : (h⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val * (h * g * h⁻¹).val * h.val =
      g.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hdet : Matrix.det (h * g * h⁻¹).val = Matrix.det g.val := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det h.val),
      mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_one]
  have hu : h * g * h⁻¹ * h = h * g := by group
  simp only [GodementJacquet.matrixIntegrand, conjTest_apply, hM, hu, determinantWeight, hdet]
  ring

end Conjugation

section ConjugationIntegral

/-- Conjugation by a fixed element preserves the normalized Haar measure. -/
theorem measurePreserving_conj (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    MeasurePreserving (fun g => h * g * h⁻¹) (generalLinearHaar F.Carrier n)
      (generalLinearHaar F.Carrier n) :=
  (measurePreserving_mul_right _ h⁻¹).comp (measurePreserving_mul_left _ h)

/-- Conjugation by a fixed element is a measurable embedding. -/
theorem measurableEmbedding_conj (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    MeasurableEmbedding fun g : Langlands.GeneralLinear (n + 1) F.Carrier => h * g * h⁻¹ :=
  (measurableEmbedding_mulRight h⁻¹).comp (measurableEmbedding_mulLeft h)

/-- Conjugation change of variables, integrability: `Φ(g) |det g|^s u(hg)` is
integrable exactly when the matrix integrand of the conjugated test against the
right translate `y ↦ u(yh)` is. -/
theorem integrable_conj_iff (Φ : MatrixTestFunction n F.Carrier)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    (u : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (s : ℂ) :
    Integrable (fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s * u (h * g))
        (generalLinearHaar F.Carrier n) ↔
      MatrixConverges F (conjTest F Φ h) s (fun y => u (y * h)) := by
  have e := (measurePreserving_conj F h).integrable_comp_emb (measurableEmbedding_conj F h)
    (g := GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
      (conjTest F Φ h) s (fun y => u (y * h)))
  have hfun : (GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
      (conjTest F Φ h) s (fun y => u (y * h)) ∘ fun g => h * g * h⁻¹) =
      fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s * u (h * g) :=
    funext fun g => matrixIntegrand_conj F Φ h u s g
  rw [hfun] at e
  exact e

/-- Conjugation change of variables, value. -/
theorem integral_conj (Φ : MatrixTestFunction n F.Carrier)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    (u : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (s : ℂ) :
    ∫ g, Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s * u (h * g)
        ∂(generalLinearHaar F.Carrier n) =
      matrixIntegral F (conjTest F Φ h) s (fun y => u (y * h)) := by
  have e := (measurePreserving_conj F h).integral_comp (measurableEmbedding_conj F h)
    (GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
      (conjTest F Φ h) s (fun y => u (y * h)))
  simp only [matrixIntegrand_conj] at e
  exact e

end ConjugationIntegral

section PointAverage

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- A vector of the coefficient model is determined by its model function. -/
theorem glModelFunction_injective (ℓ : glFunctionals ψ n σ) :
    Function.Injective (glModelFunction ψ n σ ℓ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The functional `W ↦ ∫_L W(hk) dk` on the model, for a compact open subgroup `L`. -/
def modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Module.Dual ℂ (glCoefficientModel ψ n σ ℓ).toSubmodule where
  toFun W := ∫ k in (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
    glModelFunction ψ n σ ℓ W (h * k) ∂(generalLinearHaar F.Carrier n)
  map_add' W₁ W₂ := by
    have hh : Continuous fun k : Langlands.GeneralLinear (n + 1) F.Carrier => h * k :=
      continuous_const.mul continuous_id
    have h₁ : IntegrableOn (fun k => glModelFunction ψ n σ ℓ W₁ (h * k))
        (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (generalLinearHaar F.Carrier n) :=
      ((glModelFunction_continuous ψ n σ hσ ℓ W₁).comp hh).continuousOn.integrableOn_compact'
        hL L.isOpen.measurableSet
    have h₂ : IntegrableOn (fun k => glModelFunction ψ n σ ℓ W₂ (h * k))
        (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (generalLinearHaar F.Carrier n) :=
      ((glModelFunction_continuous ψ n σ hσ ℓ W₂).comp hh).continuousOn.integrableOn_compact'
        hL L.isOpen.measurableSet
    rw [← integral_add h₁ h₂]
    rfl
  map_smul' c W := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    rfl

/-- Unfolding the point average. -/
theorem modelPointAverage_apply (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) (W : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    modelPointAverage F ψ σ hσ ℓ L hL h W =
      ∫ k in (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
        glModelFunction ψ n σ ℓ W (h * k) ∂(generalLinearHaar F.Carrier n) :=
  rfl

/-- The point average is invariant under right translation by `L`. -/
theorem modelPointAverage_invariant (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier} (hk : k ∈ L)
    (W : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ k W) =
      modelPointAverage F ψ σ hσ ℓ L hL h W := by
  rw [modelPointAverage_apply, modelPointAverage_apply]
  simp only [glModelFunction_translate]
  have e := setIntegral_mul_right_of_mem (generalLinearHaar F.Carrier n) L.toSubgroup
    L.isOpen.measurableSet hk (fun y => glModelFunction ψ n σ ℓ W (h * y))
  simp only [mul_assoc] at e ⊢
  exact e

/-- On vectors fixed by `L`, the point average is `vol(L)` times evaluation at `h`. -/
theorem modelPointAverage_of_mem_fixedVectors (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    {W : (glCoefficientModel ψ n σ ℓ).toSubmodule}
    (hW : W ∈ fixedVectors (glModelRepresentation ψ n σ ℓ) L.toSubgroup) :
    modelPointAverage F ψ σ hσ ℓ L hL h W =
      ((generalLinearHaar F.Carrier n).real (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :
        ℂ) * glModelFunction ψ n σ ℓ W h := by
  rw [modelPointAverage_apply]
  have hc : Set.EqOn (fun k => glModelFunction ψ n σ ℓ W (h * k))
      (fun _ => glModelFunction ψ n σ ℓ W h)
      (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
    intro k hk
    have e : glModelRepresentation ψ n σ ℓ k W = W := hW ⟨k, hk⟩
    have e' := congrArg (fun W' => glModelFunction ψ n σ ℓ W' h) e
    simpa only [glModelFunction_translate] using e'
  rw [setIntegral_congr_fun L.isOpen.measurableSet hc, setIntegral_const, Complex.real_smul]

/-- A compact open subgroup has nonzero finite Haar mass. -/
theorem measureReal_openSubgroup_ne_zero (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :
    ((generalLinearHaar F.Carrier n).real (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :
      ℂ) ≠ 0 := by
  have hLfin : generalLinearHaar F.Carrier n (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ≠ ⊤ :=
    hL.measure_lt_top.ne
  have hLpos : generalLinearHaar F.Carrier n (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ≠ 0 :=
    (L.isOpen.measure_pos (generalLinearHaar F.Carrier n) ⟨1, L.one_mem⟩).ne'
  rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact not_or.mpr ⟨hLpos, hLfin⟩

/-- A vector fixed by `L` on which every point average vanishes is zero. -/
theorem eq_zero_of_modelPointAverage_eq_zero (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    {W : (glCoefficientModel ψ n σ ℓ).toSubmodule}
    (hW : W ∈ fixedVectors (glModelRepresentation ψ n σ ℓ) L.toSubgroup)
    (h0 : ∀ h, modelPointAverage F ψ σ hσ ℓ L hL h W = 0) : W = 0 := by
  apply glModelFunction_injective F ψ σ ℓ
  funext h
  have h1 := h0 h
  rw [modelPointAverage_of_mem_fixedVectors F ψ σ hσ ℓ L hL h hW] at h1
  exact ((mul_eq_zero.mp h1).resolve_left (measureReal_openSubgroup_ne_zero F L hL)).trans rfl

/-- On an admissible coefficient model, every smooth functional agrees with a finite
combination of point averages over some compact open subgroup inside a prescribed
open subgroup. -/
theorem exists_eq_sum_modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (U : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) :
    ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      ∃ hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)), L ≤ U ∧
      ∃ (t : Finset (Langlands.GeneralLinear (n + 1) F.Carrier))
        (c : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ),
        ∀ W, Λ.val W = ∑ h ∈ t, c h * modelPointAverage F ψ σ hσ ℓ L hL h W := by
  obtain ⟨K₀, hK₀⟩ := Λ.property
  obtain ⟨L, hLc, hLU⟩ := Unramified.SphericalExistence.exists_compactOpenSubgroup_le F (K₀ ⊓ U)
  obtain ⟨c, hc⟩ := exists_eq_sum_of_invariant (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (glModelRepresentation ψ n σ ℓ) (glModel_isSmooth ψ n σ hσ ℓ) L hLc (hadm.2 L)
    (fun h => modelPointAverage F ψ σ hσ ℓ L hLc h)
    (fun h _ hk W => modelPointAverage_invariant F ψ σ hσ ℓ L hLc h hk W) Λ.val
    (fun _ hk W => apply_of_mem_fixedVectors_dual _ _ hK₀ (hLU hk).1 W)
    (fun e he h0 => by
      rw [eq_zero_of_modelPointAverage_eq_zero F ψ σ hσ ℓ L hLc he h0, map_zero])
  exact ⟨L, hLc, fun k hk => (hLU hk).2, c.support, c, hc⟩

end PointAverage

section ModelInclusion

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- JPSS (1983), printed 421: integrating the point average of the right translates
of a model vector against `Φ(g)|det g|^s`, for `L` fixing `Φ` on the left and inside
the kernel of `|det|`, gives `vol(L)` times the Whittaker integral of the conjugated
test function at the right translate by `h`. -/
theorem modelPointAverage_matrixIntegral (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F.Carrier)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (hLΦ : ∀ k ∈ L, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s : ℂ)
    (hconv : MatrixConverges F (conjTest F Φ h) s
      (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w))) :
    Integrable (fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w))
        (generalLinearHaar F.Carrier n) ∧
      ∫ g, Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)
        ∂(generalLinearHaar F.Carrier n) =
      ((generalLinearHaar F.Carrier n).real
          (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ) *
        matrixIntegral F (conjTest F Φ h) s
          (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w)) := by
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let abv := normalizedAbsoluteValue F.canonicalTopologicalData
  let μ := generalLinearHaar F.Carrier n
  let W := glModelFunction ψ n σ ℓ w
  let a : G → ℂ := fun g => Φ g.val * determinantWeight abv g s
  have ha : ∀ x ∈ (L : Set G), ∀ g, a (x * g) = a g := by
    intro x hx g
    obtain ⟨hΦx, hdet⟩ := hLΦ x hx
    have e : (x * g).val = x.val * g.val := rfl
    have hdet' : abv x.val.det = 1 := hdet
    show Φ (x * g).val * determinantWeight abv (x * g) s =
      Φ g.val * determinantWeight abv g s
    rw [determinantWeight, determinantWeight, e, hΦx, Matrix.det_mul, AbsoluteValue.map_mul,
      hdet', one_mul]
  have hint : Integrable (fun g => a g * W (h * g)) μ :=
    (integrable_conj_iff F Φ h W s).mpr hconv
  obtain ⟨h1, h2⟩ := leftAverage_integral μ (L : Set G) L.isOpen.measurableSet
    hL.measure_lt_top.ne a (fun x => W (h * x)) ha hint
  have hfun : (fun g => Φ g.val * determinantWeight abv g s *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)) =
      fun g => a g * ∫ x in (L : Set G), W (h * (x * g)) ∂μ := by
    funext g
    show a g * _ = a g * _
    rw [modelPointAverage_apply]
    congr 1
    refine setIntegral_congr_fun L.isOpen.measurableSet fun x _ => ?_
    show glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ g w) (h * x) =
      glModelFunction ψ n σ ℓ w (h * (x * g))
    rw [glModelFunction_translate, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact h1
  · rw [hfun, h2]
    congr 1
    exact integral_conj F Φ h W s

/-- The admissibility of `σ` passes to its coefficient model. -/
theorem glModel_isAdmissible (ℓ : glFunctionals ψ n σ) (hσ : IsAdmissible σ) :
    IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  Unramified.SphericalExistence.isAdmissible_of_surjective
    (Unramified.SphericalExistence.exists_compactOpenSubgroup_le F) (modelMap σ ℓ)
    (modelMap_surjective σ ℓ) hσ

/-- The local form of `ModelWhittakerRationalityStatement`: every shifted Whittaker
integral on the model converges on a right half-plane and is rational. -/
def ModelRationality (ℓ : glFunctionals ψ n σ) : Prop :=
  ∀ (Φ : MatrixTestFunction n F.Carrier) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule),
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => matrixIntegral F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) R

/-- A Whittaker integral of the model has a rational value lying in `I₃`, with an
explicit half-plane of convergence. -/
theorem exists_whittakerRationalValue (ℓ : glFunctionals ψ n σ) (hC : ModelRationality F ψ σ ℓ)
    (Φ : MatrixTestFunction n F.Carrier) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    ∃ (a : ℝ) (R : RationalFunctions),
      (∀ s : ℂ, a < s.re →
        MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => matrixIntegral F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) R ∧
      R ∈ whittakerRationalValues F ψ σ ℓ := by
  obtain ⟨⟨a, ha⟩, R, hR⟩ := hC Φ w
  exact ⟨a, R, ha, hR, Φ, w, ⟨a, ha⟩, hR⟩

/-- The matrix integral of a finite combination of point averages of right
translates is the corresponding combination of Whittaker integrals of conjugated
test functions, wherever all of the latter converge. -/
theorem matrixIntegral_sum_modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F.Carrier)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (hLΦ : ∀ k ∈ L, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1)
    (t : Finset (Langlands.GeneralLinear (n + 1) F.Carrier))
    (c : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ g, f g = ∑ h ∈ t, c h *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w))
    (s : ℂ)
    (hconv : ∀ h ∈ t, MatrixConverges F (conjTest F Φ h) s
      (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w))) :
    MatrixConverges F Φ s f ∧
      matrixIntegral F Φ s f =
        ∑ h ∈ t, c h * ((generalLinearHaar F.Carrier n).real
            (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ) *
          matrixIntegral F (conjTest F Φ h) s
            (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w)) := by
  have hG2 := fun h (hh : h ∈ t) =>
    modelPointAverage_matrixIntegral F ψ σ hσ ℓ Φ L hL hLΦ h w s (hconv h hh)
  have hpt : GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
      Φ s f = fun g => ∑ h ∈ t, c h * (Φ g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)) := by
    funext g
    rw [GodementJacquet.matrixIntegrand, hf g, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hint : ∀ h ∈ t, Integrable (fun g => c h * (Φ g.val *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)))
      (generalLinearHaar F.Carrier n) :=
    fun h hh => (hG2 h hh).1.const_mul (c h)
  refine ⟨?_, ?_⟩
  · show Integrable (GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s f) (generalLinearHaar F.Carrier n)
    rw [hpt]
    exact integrable_finsetSum t hint
  · show ∫ g, GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s f g
        ∂(generalLinearHaar F.Carrier n) = _
    rw [hpt, integral_finsetSum t hint]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [integral_const_mul, (hG2 h hh).2, mul_assoc]

/-- JPSS (1983), printed 421: on an admissible model with rational Whittaker
integrals, the integral of a matrix coefficient `g ↦ Λ(ρ(g)w)` of the model, for a
smooth functional `Λ`, is a finite combination of Whittaker integrals, hence has a
rational value in `I₃`. -/
theorem exists_mem_jpssI3_of_coefficient (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ)
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf₀ : ∀ g, f g = Λ.val (glModelRepresentation ψ n σ ℓ g w))
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ R ∈ jpssI3 F ψ σ ℓ,
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) Φ
        f R := by
  obtain ⟨K, -, hK⟩ := exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨L, hL, hLK, t, c, hc⟩ := exists_eq_sum_modelPointAverage F ψ σ hσ ℓ hadm Λ K
  choose a R ha hR hRmem using fun h : Langlands.GeneralLinear (n + 1) F.Carrier =>
    exists_whittakerRationalValue F ψ σ ℓ hC (conjTest F Φ h)
      (glModelRepresentation ψ n σ ℓ h w)
  have hb : ∀ h ∈ t, a h ≤ ∑ i ∈ t, |a i| := fun h hh =>
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (a i)) hh)
  have hf : ∀ g, f g = ∑ h ∈ t, c h * modelPointAverage F ψ σ hσ ℓ L hL h
      (glModelRepresentation ψ n σ ℓ g w) :=
    fun g => (hf₀ g).trans (hc _)
  have key := fun (s : ℂ) (hs : ∑ i ∈ t, |a i| < s.re) =>
    matrixIntegral_sum_modelPointAverage F ψ σ hσ ℓ Φ L hL (fun k hk => hK k (hLK hk)) t c
      w f hf (s + jpssShift n) (fun h hh => ha h s ((hb h hh).trans_lt hs))
  refine ⟨∑ h ∈ t, RatFunc.C (c h * ((generalLinearHaar F.Carrier n).real
      (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ)) * R h, ?_,
    ⟨∑ i ∈ t, |a i|, fun s hs => (key s hs).1⟩, ?_⟩
  · exact RationalContinuationLinear.linear_combination_mem_span t _ R (fun h _ => hRmem h)
  · exact RationalContinuationLinear.continuation_of_eq_on_right
      (RationalContinuationLinear.continuation_linear_combination t _ _ R (fun h _ => hR h))
      ⟨∑ i ∈ t, |a i|, fun s hs => (key s hs).2⟩

/-- Every rational value of a bi-smooth matrix-coefficient integral of the model lies
in `I₃`, given admissibility of the model and rationality of its Whittaker integrals. -/
theorem matrixRationalValues_subset_jpssI3 (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ) :
    matrixRationalValues F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) ⊆ (jpssI3 F ψ σ ℓ : Set RationalFunctions) := by
  have hP : ∀ f ∈ biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ), ∀ Φ : MatrixTestFunction n F.Carrier,
      ∃ R ∈ jpssI3 F ψ σ ℓ,
        HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
          (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
          Φ f R := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Λ, v, rfl⟩ := hx
      exact exists_mem_jpssI3_of_coefficient F ψ σ hσ ℓ hadm hC Λ v.val _
        (biSmoothCoefficient_apply _ Λ v)
    | zero => exact fun Φ => ⟨0, Submodule.zero_mem _, hasShiftedRationalValue_zero _⟩
    | add x y _ _ hx hy =>
      intro Φ
      obtain ⟨R₁, hR₁, h₁⟩ := hx Φ
      obtain ⟨R₂, hR₂, h₂⟩ := hy Φ
      exact ⟨R₁ + R₂, Submodule.add_mem _ hR₁ hR₂, h₁.add h₂⟩
    | smul c x _ hx =>
      intro Φ
      obtain ⟨R, hR, h⟩ := hx Φ
      exact ⟨RatFunc.C c * R, const_mul_mem_zetaSpan c hR, h.smul c⟩
  rintro R ⟨Φ, f, hR⟩
  obtain ⟨R', hR', h'⟩ := hP f.val f.property Φ
  rw [hR.2.unique F.canonicalTopologicalData.residueCardinality_gt_one h'.2]
  exact hR'

/-- `I₂ ⊆ I₃` for the actual coefficient model, given admissibility of the model and
rationality of its Whittaker integrals. -/
theorem jpssI2_le_jpssI3_of_rationality (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ) :
    jpssI2 F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) ≤ jpssI3 F ψ σ ℓ :=
  Submodule.span_le.mpr (matrixRationalValues_subset_jpssI3 F ψ σ hσ ℓ hadm hC)

end ModelInclusion

end Padic

/-- JPSS (1983), Section (5.2): `I₂ = I₃` on the actual coefficient model, assuming
convergence and rationality of every Whittaker integral on that model. -/
theorem whittakerModelComparison_of_rationality
    (hC : ModelWhittakerRationalityStatement.{uF, uV}) :
    WhittakerModelComparisonStatement.{uF, uV} := by
  intro p _ F ψ n V _ _ σ hW ℓ hℓ
  let := F.canonicalTopologicalData.topology
  exact le_antisymm
    (Padic.jpssI2_le_jpssI3_of_rationality F ψ σ hW.1.1 ℓ
      (Padic.glModel_isAdmissible F ψ σ ℓ hW.1) (hC p F ψ n σ hW ℓ hℓ))
    (Padic.jpssI3_le_jpssI2 F ψ σ hW.1.1 ℓ)

end Langlands.GodementJacquet
