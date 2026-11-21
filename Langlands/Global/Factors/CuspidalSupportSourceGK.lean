import Langlands.Global.Factors.CuspidalSupportIdentityEvaluation
import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation

/-! # Place module laws for compact-finite automorphic operator sources -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean Langlands.GeneralLinear ArchimedeanGL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1100000

attribute [local instance 100] LieRing.ofAssociativeRing

section WeakContinuity

variable {K V W : Type*} [Monoid K] [TopologicalSpace K]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Each algebraic linear functional of each compact orbit is continuous. -/
def HasWeaklyContinuousOrbits (ρ : Representation ℂ K W) : Prop :=
  ∀ (w : W) (μ : W →ₗ[ℂ] ℂ), Continuous fun k => μ (ρ k w)

/-- Weak continuity restricts along an injective representation intertwiner. -/
theorem HasWeaklyContinuousOrbits.of_injective_intertwiner
    {ρ : Representation ℂ K V} {τ : Representation ℂ K W}
    (j : Representation.IntertwiningMap ρ τ) (hj : Function.Injective j.toLinearMap)
    (hτ : HasWeaklyContinuousOrbits τ) : HasWeaklyContinuousOrbits ρ := by
  intro v μ
  let b := LinearEquiv.ofInjective j.toLinearMap hj
  obtain ⟨ν, hν⟩ := LinearMap.exists_extend (μ.comp b.symm.toLinearMap)
  have extend_apply (x : V) : ν (j.toLinearMap x) = μ x := by
    change ν (b x).val = μ x
    have h := LinearMap.congr_fun hν (b x)
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  have h (k : K) : ν (τ k (j.toLinearMap v)) = μ (ρ k v) := by
    change ν (τ k (j v)) = μ (ρ k v)
    rw [← Representation.IntertwiningMap.isIntertwining ρ τ j]
    exact extend_apply _
  rw [← funext h]
  exact hτ _ ν

/-- Weak continuity descends through a spanning family of representation images. -/
theorem HasWeaklyContinuousOrbits.of_spanning_ranges
    {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (ρ : ∀ i, Representation ℂ K (E i)) (τ : Representation ℂ K W)
    (j : ∀ i, Representation.IntertwiningMap (ρ i) τ)
    (hspan : (⨆ i, (j i).toLinearMap.range) = ⊤)
    (hρ : ∀ i, HasWeaklyContinuousOrbits (ρ i)) : HasWeaklyContinuousOrbits τ := by
  intro w μ
  have hw : w ∈ ⨆ i, (j i).toLinearMap.range := by rw [hspan]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun x => Continuous fun k => μ (τ k x))
    hw ?_ ?_ ?_
  · rintro i _ ⟨x, rfl⟩
    have h (k : K) : μ (τ k ((j i).toLinearMap x)) = (μ.comp (j i).toLinearMap) (ρ i k x) := by
      exact congrArg (fun y : W => μ y)
        (Representation.IntertwiningMap.isIntertwining (ρ i) τ (j i) k x).symm
    rw [funext h]
    exact hρ i x _
  · simpa only [map_zero] using (continuous_const : Continuous fun _ : K => (0 : ℂ))
  · intro x y hx hy
    simpa only [map_add] using
      (show Continuous (fun k : K => μ (τ k x) + μ (τ k y)) from hx.add hy)

end WeakContinuity

section PlaceLaws

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {W : Type u} [AddCommGroup W] [Module ℂ W]

local instance sourceGKRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance sourceGKContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance sourceGKSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance sourceGKOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)

private abbrev sourceGKComplexLie : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ W :=
  ((A.comp (differentialOperator F n)).toLieHom).comp (envelopingGenerator F n)

local notation "κ" => A.toMonoidHom.comp (compactOperator F n)
local notation "D" => sourceGKComplexLie A
local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

private theorem compact_orbit_finite_comp {K : Type*} [Monoid K]
    (f : K →* standardInfiniteCompact F n) (w : W) (h : FiniteVectors.IsFiniteVector κ w) :
    FiniteVectors.IsFiniteVector ((κ).comp f) w := by
  let _ : Module.Finite ℂ (FiniteVectors.orbitSpan κ w) := h
  have hs : FiniteVectors.orbitSpan ((κ).comp f) w ≤ FiniteVectors.orbitSpan κ w := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact FiniteVectors.action_mem_orbitSpan κ (f k) w
  exact Submodule.finiteDimensional_of_le hs

private theorem sourceCompact_differential_covariance
    (k : standardInfiniteCompact F n) (X Y : ComplexLieAlgebra F n)
    (h : complexLieConjugation F n k.val X = Y) (w : W) :
    κ k (D X w) = D Y (κ k w) := by
  have hc := compactOperator_differentialOperator_covariance k (envelopingGenerator F n X)
  rw [envelopingConjugation_generator, h] at hc
  have hA := LinearMap.congr_fun (congrArg (fun a : automorphicOperatorAlgebra F n => A a) hc) w
  change A (compactOperator F n k) (A (differentialOperator F n (envelopingGenerator F n X)) w) =
    A (differentialOperator F n (envelopingGenerator F n Y)) (A (compactOperator F n k) w)
  simpa only [map_mul, Module.End.mul_apply] using hA

/-- Full compact finiteness, weak continuity and differentiation give the
real-place module laws for an action of the genuine operator algebra. -/
theorem source_isRealGKModule (v : RP)
    (hfin : ∀ w : W, FiniteVectors.IsFiniteVector κ w)
    (hcont : HasWeaklyContinuousOrbits κ) (hder : CompactDualDerivative κ D) :
    IsRealGKModule n (sourceRealPlaceCompact A v) (sourceRealPlaceLie A v) := by
  refine ⟨fun w => compact_orbit_finite_comp A (realPlaceCompactInclusion F n v).toMonoidHom
    w (hfin w), fun w μ => (hcont w μ).comp (realPlaceCompactInclusion F n v).continuous, ?_, ?_⟩
  · intro γ X hγ0 hγ w μ
    exact hder (realPlaceLieInclusion F n v X)
      (fun t => realPlaceCompactInclusion F n v (γ t)) (by simp [hγ0])
      (hasDerivAt_coordinates_realPlaceCompactInclusion v γ X hγ) μ w
  · intro k X w
    apply sourceCompact_differential_covariance
    have h := complexLieConjugation_realInclusion F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) v (1 ⊗ₜ[ℝ] X)
    simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same,
      unitaryMatrixComplexLieConjugation_tmul, unitaryMatrixRealLieConjugation_apply] using! h

/-- The same restriction at a complex place uses the full real tangent space
of the complex matrix group. -/
theorem source_isComplexGKModule (v : CP)
    (hfin : ∀ w : W, FiniteVectors.IsFiniteVector κ w)
    (hcont : HasWeaklyContinuousOrbits κ) (hder : CompactDualDerivative κ D) :
    IsComplexGKModule n (sourceComplexPlaceCompact A v) (sourceComplexPlaceLie A v) := by
  refine ⟨fun w => compact_orbit_finite_comp A (complexPlaceCompactInclusion F n v).toMonoidHom
    w (hfin w), fun w μ => (hcont w μ).comp (complexPlaceCompactInclusion F n v).continuous, ?_, ?_⟩
  · intro γ X hγ0 hγ w μ
    exact hder (complexPlaceLieInclusion F n v X)
      (fun t => complexPlaceCompactInclusion F n v (γ t)) (by simp [hγ0])
      (hasDerivAt_coordinates_complexPlaceCompactInclusion v γ X hγ) μ w
  · intro k X w
    apply sourceCompact_differential_covariance
    have h := complexLieConjugation_complexInclusion F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) v (1 ⊗ₜ[ℝ] X)
    simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same,
      unitaryMatrixComplexLieConjugation_tmul, unitaryMatrixRealLieConjugation_apply] using! h

end PlaceLaws

end Langlands.Global
