import Langlands.Representation.Whittaker.AsymptoticStatement
import Langlands.Representation.Whittaker.CoefficientCentralCharacterProof
import Langlands.Representation.Whittaker.LastEntryOneAssembly
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.RankinSelberg.FiniteFunctionClosureProof

/-!
# Extending the Whittaker expansion to the full diagonal torus

Normalize the last entry, then use the common central character of all
Whittaker coefficient images. Finite-function closure and finite-fiber
regrouping preserve the uniform finite family and Schwartz–Bruhat coefficients.
-/

noncomputable section

namespace Langlands.WhittakerLastEntryOne

open scoped BigOperators

universe uA uB uK uV

theorem IsFiniteFunction.comp {A : Type uA} {B : Type uB}
    [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
    {f : B → ℂ} (hf : IsFiniteFunction f) (q : A →* B) (hq : Continuous q) :
    IsFiniteFunction (fun a => f (q a)) :=
  (RankinSelberg.finiteFunctionClosure B A).2.1 q hq f hf

theorem IsFiniteFunction.mul {A : Type uA} [Monoid A] [TopologicalSpace A]
    {f g : A → ℂ} (hf : IsFiniteFunction f) (hg : IsFiniteFunction g) :
    IsFiniteFunction (fun a => f a * g a) :=
  (RankinSelberg.finiteFunctionClosure A A).1 f g hf hg

end Langlands.WhittakerLastEntryOne

namespace Langlands.WhittakerFullTorus

open scoped BigOperators
open Langlands.WhittakerLastEntryOne (IsFiniteFunction torus roots)

universe uA uB uK uV

section Torus

variable {K : Type uK} [Field K] {n : ℕ}

/-- The last diagonal entry. -/
def lastCoord : (Fin (n + 1) → Kˣ) →* Kˣ where
  toFun a := a (Fin.last n)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Divide every diagonal entry by the last one. -/
def normalize : (Fin (n + 1) → Kˣ) →* (Fin (n + 1) → Kˣ) where
  toFun a i := a i / a (Fin.last n)
  map_one' := by ext i; simp
  map_mul' a b := by
    funext i
    change (a i * b i) / (a (Fin.last n) * b (Fin.last n)) =
      (a i / a (Fin.last n)) * (b i / b (Fin.last n))
    exact mul_div_mul_comm _ _ _ _

@[simp] theorem normalize_last (a : Fin (n + 1) → Kˣ) :
    normalize a (Fin.last n) = 1 := by
  change a (Fin.last n) / a (Fin.last n) = 1
  exact div_self' _

@[simp] theorem roots_normalize (a : Fin (n + 1) → Kˣ) :
    roots (normalize a) = roots a := by
  funext i
  simp [roots, WhittakerLastEntryOne.rootHom, normalize, div_div_div_cancel_right]

@[simp] theorem torus_const (z : Kˣ) :
    torus (fun _ : Fin (n + 1) => z) = GeneralLinear.scalar z := by
  apply Units.ext
  ext i j
  simp [torus, GeneralLinear.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- The full torus factors through a last-entry-one torus and a scalar. -/
theorem torus_factor (a : Fin (n + 1) → Kˣ) :
    torus a = torus (normalize a) * GeneralLinear.scalar (lastCoord a) := by
  rw [← torus_const, ← map_mul]
  congr 1
  ext i
  simp [normalize, lastCoord]

/-- The same factorization with the scalar on the left. -/
theorem torus_factor_left (a : Fin (n + 1) → Kˣ) :
    torus a = GeneralLinear.scalar (lastCoord a) * torus (normalize a) := by
  rw [torus_factor, ← torus_const, ← map_mul, ← map_mul, mul_comm]

variable [TopologicalSpace K]

/-- Scalar matrices give the continuous map into the actual center. -/
theorem continuous_scalarToCenter :
    Continuous (GeneralLinear.scalarToCenter (R := K) (n := n + 1)) :=
  GeneralLinear.scalarContinuous.continuous.subtype_mk _

theorem continuous_lastCoord : Continuous (lastCoord (K := K) (n := n)) :=
  continuous_apply _

variable [IsTopologicalRing K]

theorem continuous_normalize : Continuous (normalize (K := K) (n := n)) := by
  apply continuous_pi
  intro i
  change Continuous (fun a : Fin (n + 1) → Kˣ => a i / a (Fin.last n))
  exact (continuous_apply i).div' (continuous_apply (Fin.last n))

/-- Every paired coefficient in the full-torus extension is a finite function. -/
theorem finiteFunction_product {η : Kˣ → ℂ}
    {χ : (Fin (n + 1) → Kˣ) → ℂ}
    (hη : IsFiniteFunction η) (hχ : IsFiniteFunction χ) :
    IsFiniteFunction (fun a => η (lastCoord a) * χ (normalize a)) :=
  (hη.comp lastCoord continuous_lastCoord).mul (hχ.comp normalize continuous_normalize)

end Torus

/-- The normalization uses exactly the canonical topology of the target. -/
theorem canonical_continuous_normalize (p : ℕ) [Fact p.Prime]
    (F : PadicField.{uK} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    Continuous (normalize (K := F.Carrier) (n := n)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact continuous_normalize

/-- Equal finite functions are combined by summing their Schwartz coefficients. -/
theorem regroup {ι : Type*} {A : Type uA} {B : Type uB} [TopologicalSpace B]
    [DecidableEq (A → ℂ)] (s : Finset ι) (f : ι → A → ℂ)
    (φ : ι → HarmonicAnalysis.SchwartzBruhat B) :
    ∃ Φ : (A → ℂ) → HarmonicAnalysis.SchwartzBruhat B,
      ∀ a b, (∑ i ∈ s, φ i b * f i a) = ∑ χ ∈ s.image f, Φ χ b * χ a := by
  classical
  refine ⟨fun χ => ∑ i ∈ s.filter (fun i => f i = χ), φ i, ?_⟩
  intro a b
  rw [← Finset.sum_fiberwise_of_maps_to (g := f)
    (fun i hi => Finset.mem_image_of_mem f hi) (fun i => φ i b * f i a)]
  apply Finset.sum_congr rfl
  intro χ hχ
  have heval : (∑ i ∈ s.filter (fun i => f i = χ), φ i) b =
      ∑ i ∈ s.filter (fun i => f i = χ), φ i b := by
    simp only [Submodule.coe_sum, Finset.sum_apply]
  rw [heval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- A character law on actual coefficient images gives the functional scalar law. -/
theorem functional_scalarLaw_of_coefficientLaw
    {K : Type uK} [Field K] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
    (N : Subgroup (GeneralLinear (n + 1) K)) (θ : N →* ℂˣ)
    (η : Subgroup.center (GeneralLinear (n + 1) K) →* ℂˣ)
    (hη : ∀ (ℓ : Whittaker.functionals N θ ρ)
      (f : (Whittaker.coefficientModel ρ ℓ).toSubmodule)
      (z : Subgroup.center (GeneralLinear (n + 1) K)) (g : GeneralLinear (n + 1) K),
      f.val.val ((z : GeneralLinear (n + 1) K) * g) = (η z : ℂ) * f.val.val g)
    (ℓ : Whittaker.functionals N θ ρ) (z : Kˣ) (v : V) :
    ℓ.val (ρ (GeneralLinear.scalar z) v) =
      (η (GeneralLinear.scalarToCenter z) : ℂ) * ℓ.val v := by
  have h := hη ℓ (Whittaker.modelMap ρ ℓ v) (GeneralLinear.scalarToCenter z) 1
  change ℓ.val (ρ (GeneralLinear.scalar z * 1) v) =
    (η (GeneralLinear.scalarToCenter z) : ℂ) * ℓ.val (ρ 1 v) at h
  simpa using h

/-- Convert the target's nonzero spanning-functional hypothesis to the character interface. -/
theorem scalarCharacter_of_spanning_functional
    {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (hcharacter : Whittaker.CoefficientCentralCharacterStatement.{uK, uV}
      (GeneralLinear (n + 1) K))
    (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
    (N : Subgroup (GeneralLinear (n + 1) K)) (θ : N →* ℂˣ)
    (hρ : IsSmooth ρ)
    (hspan : ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ ℓ ∈ Whittaker.functionals N θ ρ ∧
      ∀ ℓ' : Module.Dual ℂ V, ℓ' ∈ Whittaker.functionals N θ ρ →
        ∃ c : ℂ, ℓ' = c • ℓ) :
    ∃ η : Kˣ →* ℂ, Continuous η ∧
      ∀ ℓ : Module.Dual ℂ V, ℓ ∈ Whittaker.functionals N θ ρ → ∀ z v,
        ℓ (ρ (GeneralLinear.scalar z) v) = η z * ℓ v := by
  obtain ⟨ℓ₀, hℓ₀, hmem, hspan⟩ := hspan
  let W := Whittaker.functionals N θ ρ
  let w : W := ⟨ℓ₀, hmem⟩
  have hw : w ≠ 0 := by
    intro h
    exact hℓ₀ (congrArg Subtype.val h)
  let f : ℂ →ₗ[ℂ] W := LinearMap.toSpanSingleton ℂ W w
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact smul_left_injective ℂ hw hab
    · intro w'
      obtain ⟨c, hc⟩ := hspan w'.val w'.property
      exact ⟨c, Subtype.ext hc.symm⟩
  have hdim : Nonempty (W ≃ₗ[ℂ] ℂ) := ⟨(LinearEquiv.ofBijective f hf).symm⟩
  obtain ⟨χ, hχ, _⟩ := hcharacter N θ V ρ hρ hdim
  let η : Kˣ →* ℂ :=
    (Units.coeHom ℂ).comp (χ.comp (GeneralLinear.scalarToCenter (n := n + 1)))
  refine ⟨η, ?_, ?_⟩
  · exact Units.continuous_val.comp (hχ.1.continuous.comp continuous_scalarToCenter)
  · intro ℓ hℓ z v
    exact functional_scalarLaw_of_coefficientLaw ρ N θ χ hχ.2 ⟨ℓ, hℓ⟩ z v

/-- A common character on eligible coefficients suffices for full-torus assembly. -/
theorem extend_of_coefficient_character
    {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
    (eligible : Module.Dual ℂ V → Prop)
    (X : Finset ((Fin (n + 1) → Kˣ) → ℂ))
    (hX : ∀ χ ∈ X, IsFiniteFunction χ)
    (hred : ∀ ℓ : Module.Dual ℂ V, eligible ℓ → ∀ v : V,
      ∃ φ : ((Fin (n + 1) → Kˣ) → ℂ) →
          HarmonicAnalysis.SchwartzBruhat (Fin n → K),
        ∀ a, a (Fin.last n) = 1 →
          ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a)
    (η : Kˣ →* ℂ) (hη : Continuous η)
    (hcentral : ∀ ℓ : Module.Dual ℂ V, eligible ℓ → ∀ z v,
      ℓ (ρ (GeneralLinear.scalar z) v) = η z * ℓ v) :
    ∃ Z : Finset ((Fin (n + 1) → Kˣ) → ℂ),
      (∀ χ ∈ Z, IsFiniteFunction χ) ∧
      ∀ ℓ : Module.Dual ℂ V, eligible ℓ → ∀ v : V,
        ∃ Φ : ((Fin (n + 1) → Kˣ) → ℂ) →
            HarmonicAnalysis.SchwartzBruhat (Fin n → K),
          ∀ a, ℓ (ρ (torus a) v) = ∑ χ ∈ Z, Φ χ (roots a) * χ a := by
  classical
  let f : ((Fin (n + 1) → Kˣ) → ℂ) → ((Fin (n + 1) → Kˣ) → ℂ) :=
    fun χ a => η (lastCoord a) * χ (normalize a)
  have hηfinite : IsFiniteFunction (η : Kˣ → ℂ) :=
    (RankinSelberg.finiteFunctionClosure Kˣ Kˣ).2.2 η hη
  refine ⟨X.image f, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hχ
    exact finiteFunction_product hηfinite (hX ξ hξ)
  · intro ℓ hℓ v
    obtain ⟨φ, hφ⟩ := hred ℓ hℓ v
    obtain ⟨Φ, hΦ⟩ := regroup X f φ
    refine ⟨Φ, ?_⟩
    intro a
    calc
      ℓ (ρ (torus a) v) =
          η (lastCoord a) * ℓ (ρ (torus (normalize a)) v) := by
        rw [torus_factor_left, map_mul, Module.End.mul_apply, hcentral ℓ hℓ]
      _ = η (lastCoord a) *
          (∑ χ ∈ X, φ χ (roots a) * χ (normalize a)) := by
        rw [hφ (normalize a) (normalize_last a), roots_normalize]
      _ = ∑ χ ∈ X, φ χ (roots a) * f χ a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ hχ
        dsimp [f]
        ring
      _ = ∑ χ ∈ X.image f, Φ χ (roots a) * χ a := hΦ a (roots a)

/-- The exact last-entry-one target implies the unchanged full-torus target. -/
theorem of_lastEntryOne
    (hred : WhittakerLastEntryOneAsymptoticStatement.{uK, uV}) :
    WhittakerTypeAsymptoticStatement.{uK, uV} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro n V _ _ ρ ψ hcont hne hu hadm hfin
  dsimp only
  intro hspan
  let eligible : Module.Dual ℂ V → Prop := fun ℓ =>
    ∀ g : GeneralLinear (n + 1) F.Carrier,
      ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
      ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v
  have hmem (ℓ : Module.Dual ℂ V) :
      ℓ ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (Whittaker.entrywiseCharacter ψ (n + 1)) ρ ↔ eligible ℓ := by
    simpa only [eligible, Whittaker.EntrywiseEquivariant, and_imp] using
      Whittaker.mem_functionals_entrywiseCharacter_iff_entrywise ψ n ρ ℓ
  have hspan' : ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧
      ℓ ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (Whittaker.entrywiseCharacter ψ (n + 1)) ρ ∧
      ∀ ℓ' : Module.Dual ℂ V,
        ℓ' ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
          (Whittaker.entrywiseCharacter ψ (n + 1)) ρ →
        ∃ c : ℂ, ℓ' = c • ℓ := by
    obtain ⟨ℓ, hne, heq, hspan⟩ := hspan
    exact ⟨ℓ, hne, (hmem ℓ).mpr heq,
      fun ℓ' hℓ' => hspan ℓ' ((hmem ℓ').mp hℓ')⟩
  obtain ⟨η, hη, hcentral⟩ := scalarCharacter_of_spanning_functional
    (Whittaker.coefficientCentralCharacter (GeneralLinear (n + 1) F.Carrier))
    ρ (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
    (Whittaker.entrywiseCharacter ψ (n + 1)) hadm.1 hspan'
  obtain ⟨X, hX, hredX⟩ := hred p hp F n V ρ ψ hcont hne hu hadm hfin hspan
  exact extend_of_coefficient_character ρ eligible X hX hredX η hη
    (fun ℓ hℓ => hcentral ℓ ((hmem ℓ).mpr hℓ))

end Langlands.WhittakerFullTorus
