import Langlands.Global.AdelicEisensteinLinearConvergence
import Langlands.Global.EisensteinConvergenceAnchors
import Langlands.Global.EisensteinOperatorContinuation
import Langlands.Global.EisensteinOperatorCoefficients

/-! # Scalar identities for finite combinations of Eisenstein seed operators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.Global.EisensteinJet

open AdelicGroupPoints Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.Meromorphic UniformGrowthFrechetSpace

private theorem eisensteinSeries_sum_smul
    {F : Type u} [Field F] [NumberField F]
    {G P : GroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    {I : Type*} [Fintype I] (c : I → ℂ) (φ : I → AdelicGroupPoints F G → ℂ)
    (hφ : ∀ i, φ i ∈ hK.compactMajorantSections lam) :
    hK.eisensteinSeries (∑ i, c i • φ i) lam = ∑ i, c i • hK.eisensteinSeries (φ i) lam := by
  let v (i : I) : hK.compactMajorantSections lam := ⟨φ i, hφ i⟩
  calc
    _ = hK.eisensteinSeries (↑(∑ i, c i • v i)) lam := by
      congr 1
      simp [v]
    _ = _ := by
      change hK.eisensteinSeriesLinear lam (∑ i, c i • v i) =
        ∑ i, c i • hK.eisensteinSeriesLinear lam (v i)
      simp only [map_sum, map_smul]

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance seedOperatorGeneralLinearIsAffine : IsAffine (GL[F, n]).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GL[F, n]
local notation "Operators" => FreeOperatorAlgebra F n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

/-- Apply each entry of a finitely supported free-operator vector to the
corresponding scalar continued seed value. -/
def scalarSeedOperatorCombination (f : Fin m → E → Adeles → ℂ)
    (w : Fin m →₀ Operators) (t : E) : Adeles → ℂ :=
  ∑ i, scalarAutomorphicOperator F n (freeOperatorProjection F n (w i)) (f i t)

/-- Finite word covariance and convergence of the constant sections identify
the operator combination with the sum on its entire section curve. -/
theorem eventually_scalarSeedOperatorCombination_eq
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (ℱ : Filter E) (e : E → ComplexCharacterParameter F P)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Adeles → ℂ))
    (T : E → Operators →ₐ[ℂ] Module.End ℂ V)
    (hMajor : ∀ v, ∀ᶠ t in ℱ, j v ∈ hK.compactMajorantSections (e t))
    (hHol : ∀ a v, (fun t => T t a v) ∈ finiteHolomorphicSections E V)
    (hWord : ∀ a v, ∀ᶠ t in ℱ, scalarAutomorphicOperator F n (freeOperatorProjection F n a)
        (hK.eisensteinSeries (j v) (e t)) = hK.eisensteinSeries (j (T t a v)) (e t))
    (v : Fin m → V) (f : Fin m → E → Adeles → ℂ)
    (hf : ∀ i, ∀ᶠ t in ℱ, f i t = hK.eisensteinSeries (j (v i)) (e t))
    (w : Fin m →₀ Operators) (c : E → Fin m → ℂ)
    (hc : ∀ t, operatorLinearCombination (T t) v w = ∑ i, c t i • v i) :
    ∀ᶠ t in ℱ, scalarSeedOperatorCombination F n f w t = continuedLinearCombination f t (c t) := by
  have hv : ∀ᶠ t in ℱ, ∀ i, j (v i) ∈ hK.compactMajorantSections (e t) :=
    eventually_all.mpr fun i => hMajor (v i)
  have hvw : ∀ᶠ t in ℱ, ∀ i, j (T t (w i) (v i)) ∈ hK.compactMajorantSections (e t) :=
    eventually_all.mpr fun i =>
      eventually_mem_of_finiteHolomorphicSections ℱ
        (fun t => (hK.compactMajorantSections (e t)).comap j) hMajor (hHol (w i) (v i))
  filter_upwards [hv, hvw, eventually_all.mpr hf, eventually_all.mpr (fun i => hWord (w i) (v i))]
    with t hV hW hF hA
  have hw : operatorLinearCombination (T t) v w = ∑ i, T t (w i) (v i) := by
    rw [operatorLinearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp only [map_zero, LinearMap.zero_apply]
  calc
    _ = ∑ i, hK.eisensteinSeries (j (T t (w i) (v i))) (e t) :=
      Finset.sum_congr rfl fun i _ => by rw [hF i, hA i]
    _ = hK.eisensteinSeries (j (operatorLinearCombination (T t) v w)) (e t) := by
      rw [hw, map_sum]
      symm
      simpa only [one_smul] using eisensteinSeries_sum_smul hK (e t)
        (fun _ : Fin m => 1) (fun i => j (T t (w i) (v i))) hW
    _ = _ := by
      rw [hc t, map_sum]
      simp only [map_smul, continuedLinearCombination_apply, hF]
      exact eisensteinSeries_sum_smul hK (e t) (c t) (fun i => j (v i)) hV

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)

local notation "Growth[" R "," L "]" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "value[" R "," L "]" => UniformGrowthFrechetSpace.toFun F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "test[" R "," L "]" => generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L

/-- Continue the scalar seed-operator identity from its open anchor to the
normalization ball using the same free coefficients as the Taylor tests. -/
theorem normalized_seedOperatorCombination_eqOn_of_anchor
    (f : Fin m → E → Adeles → ℂ) (w : Fin m →₀ Operators)
    (hlocal : ∀ i z, ∃ B : TopologicalSpace.Opens E, z ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n])) ∧
        ∃ (v : B → Growth[R, L]) (D : Set B), IsMeromorphicOn 𝓘(ℂ, E) v D ∧
          ∀ t ∈ D, value[R, L] (v t) = f i t.val)
    (c : E → Fin m → ℂ) (hc : ∀ i, Differentiable ℂ (fun t => c t i))
    {C : Set E} (hC : IsOpen C) (hne : C.Nonempty)
    (hanchor : ∀ t ∈ C, scalarSeedOperatorCombination F n f w t = continuedLinearCombination f t (c t))
    {z : E} {r : ℝ} (hr : 0 < r) (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
    (J : E → (Fin m → ℂ) →ₗ[ℂ] Growth[R, L]) (b : E → ℂ)
    (hb : DifferentiableOn ℂ b (Metric.ball z r))
    (hJ : ∀ v (l : Growth[R, L] →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => l (J t v)) (Metric.ball z r))
    {V : Set E} (hV : IsOpen V) (hsub : V ⊆ Metric.ball z r) (hcl : Metric.ball z r ⊆ closure V)
    (hEq : ∀ t ∈ V, b t ≠ 0 ∧ ∀ v, value[R, L] (J t v) = b t • continuedLinearCombination f t v)
    (x : Adeles) :
    EqOn (fun t => w.sum fun i a => test[R, L] (freeOperatorProjection F n a) x (J t (Pi.single i 1)))
      (fun t => value[R, L] (J t (c t)) x) (Metric.ball z r) := by
  have heq := normalized_operatorCombination_eqOn_of_anchor F n rho hsmooth hcalc hN hrho
    (fun i => freeOperatorProjection F n (w i)) f hlocal c hc hC hne
    (fun t ht x => by simpa only [scalarSeedOperatorCombination, Finset.sum_apply] using congrFun (hanchor t ht) x)
    hr R L J b hb hJ hV hsub hcl hEq x
  intro t ht
  change w.sum (fun i a => test[R, L] (freeOperatorProjection F n a) x (J t (Pi.single i 1))) = _
  rw [Finsupp.sum_fintype]
  · exact heq ht
  · intro i
    rw [map_zero, generalLinearOperatorEvaluation_apply]
    rfl

end Langlands.Global.EisensteinJet
