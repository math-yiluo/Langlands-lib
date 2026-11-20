import Langlands.Representation.Archimedean.RealPrincipalSeriesFrobeniusClosure
import Langlands.Representation.Archimedean.SmoothHilbert

/-! # The algebraic Frobenius map into the genuine smooth Hilbert carrier -/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

attribute [local instance 100] LieRing.ofAssociativeRing

open RealJacquetFrobenius

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "I" => matrixModel ℝ n
local notation "K" => unitaryCompact ℝ n

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ
local notation "j" => frobeniusClosureMap hgk hℓ

private theorem frobeniusHilbert_ne_zero (h₀ : ℓ ≠ 0) : frobeniusHilbert hgk hℓ ≠ 0 := by
  intro h
  apply h₀
  apply LinearMap.ext
  intro v
  have hz : embed a e (frobeniusPrincipalSeries hgk hℓ v) = embed a e 0 := by
    simpa only [frobeniusHilbert, LinearMap.comp_apply, map_zero, LinearMap.zero_apply] using
      LinearMap.congr_fun h v
  have heq := embed_injective a e hz
  have hzero : frobFun ρ ℓ a e v 1 = 0 := congrFun (congrArg Subtype.val heq) 1
  have hsign (i : Fin n) (w : V) : ℓ (ρ (signReflection n i) w) = (-1) ^ (e i).val * ℓ w :=
    (hℓ.2 i w).2
  have hval : frobFun ρ ℓ a e v 1 = ℓ v := by
    rw [frobFun_eq (b := 1) (k := 1) hsign Matrix.blockTriangular_one (one_mem _) (by simp) v,
      diagChar_one, one_mul]
    change ℓ (ρ 1 v) = ℓ v
    rw [map_one, Module.End.one_apply]
  exact hval.symm.trans hzero

/-- A nonzero Jacquet functional gives an injective Hilbert map on an irreducible GK module. -/
theorem frobeniusHilbert_injective (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) :
    Function.Injective (frobeniusHilbert hgk hℓ) := by
  let B := frobeniusHilbert hgk hℓ
  apply LinearMap.ker_eq_bot.mp
  have hK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) (hv : v ∈ LinearMap.ker B) :
      ρ k v ∈ LinearMap.ker B := by
    let k' : K := ⟨Unitary.toUnits k, k.2⟩
    have he : representation a e (k' : GL) (B v) = B (ρ k v) :=
      representation_frobeniusHilbert_compact hgk hℓ k' v
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← he, hv, map_zero]
  have hLie (Z : ℂ ⊗[ℝ] Mat) (v : V) (hv : v ∈ LinearMap.ker B) :
      π Z v ∈ LinearMap.ker B := by
    have hReal (X : Mat) : π (1 ⊗ₜ X) v ∈ LinearMap.ker B := by
      rw [LinearMap.mem_ker] at hv ⊢
      change frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v) = 0
      rw [← lieDerivative_frobeniusHilbert hgk hℓ, show frobeniusHilbert hgk hℓ v = 0 from hv]
      have hzero : orbitMap (representation a e) (0 : Hilbert a e) = fun _ => 0 :=
        funext fun g => map_zero (representation a e g)
      rw [lieDerivative, hzero]
      simp
    refine TensorProduct.inductionOn (motive := fun Z => π Z v ∈ LinearMap.ker B) Z ?_ ?_
    · intro c X
      have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply]
      exact (LinearMap.ker B).smul_mem c (hReal X)
    · intro Z₁ Z₂ h₁ h₂
      rw [map_add, LinearMap.add_apply]
      exact (LinearMap.ker B).add_mem h₁ h₂
  rcases hirr.2 (LinearMap.ker B) hK hLie with hker | hker
  · exact hker
  · exact (frobeniusHilbert_ne_zero hgk hℓ h₀ (LinearMap.ker_eq_top.mp hker)).elim

theorem frobeniusClosureMap_injective (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) :
    Function.Injective j := by
  intro v w he
  exact frobeniusHilbert_injective hgk hℓ hirr h₀ (congrArg Subtype.val he)

private theorem project_frobeniusOrbit (g : GL) (v : V) :
    (frobeniusClosure hgk hℓ).orthogonalProjectionOnto
      (representation a e g (frobeniusHilbert hgk hℓ v)) = R g (j v) :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (R g (j v))

/-- Frobenius vectors remain smooth for the action restricted to their Hilbert closure. -/
theorem isSmoothVector_frobeniusClosureMap (v : V) : IsSmoothVector I (E := W) R (j v) := by
  let P := ((frobeniusClosure hgk hℓ).orthogonalProjectionOnto).restrictScalars ℝ
  have hP : ContMDiff 𝓘(ℝ, Hilbert a e) 𝓘(ℝ, W) ∞ P := P.contDiff.contMDiff
  have h : orbitMap R (j v) = P ∘ orbitMap (representation a e) (frobeniusHilbert hgk hℓ v) :=
    funext fun g => (project_frobeniusOrbit hgk hℓ g v).symm
  unfold IsSmoothVector
  rw [h]
  exact hP.comp (isSmoothVector_frobeniusHilbert hgk hℓ v)

private theorem lieDerivative_comp_orbit {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R₁ : GL →* (E →L[ℂ] E)) (R₂ : GL →* (H →L[ℂ] H)) (P : E →L[ℝ] H)
    {x : E} {y : H} (hx : IsSmoothVector I R₁ x)
    (h : orbitMap R₂ y = P ∘ orbitMap R₁ x) (X : Mat) :
    lieDerivative I R₂ X y = P (lieDerivative I R₁ X x) := by
  have hd : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap R₁ x) (1 : GL) :=
    hx.mdifferentiableAt (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, H) P (orbitMap R₁ x 1) :=
    P.differentiableAt.mdifferentiableAt
  unfold lieDerivative
  rw [h, mfderiv_comp 1 hP hd, ContinuousLinearMap.mfderiv_eq]
  rfl

/-- The genuine Lie derivative in the closure is the Frobenius image of the given Lie action. -/
theorem lieDerivative_frobeniusClosureMap (X : Mat) (v : V) :
    lieDerivative I (E := W) R X (j v) = j (π (1 ⊗ₜ X) v) := by
  let P := ((frobeniusClosure hgk hℓ).orthogonalProjectionOnto).restrictScalars ℝ
  let T := orbitMap (representation a e) (frobeniusHilbert hgk hℓ v)
  have h : orbitMap R (j v) = P ∘ T := funext fun g => (project_frobeniusOrbit hgk hℓ g v).symm
  calc
    _ = P (lieDerivative I (representation a e) X (frobeniusHilbert hgk hℓ v)) :=
      lieDerivative_comp_orbit (H := W) (representation a e) R P
        (isSmoothVector_frobeniusHilbert hgk hℓ v) h X
    _ = P (frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v)) := by
      rw [lieDerivative_frobeniusHilbert hgk hℓ]
    _ = _ := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (j (π (1 ⊗ₜ X) v))

private def liftToDerivativeSmoothVectors {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (A : GL →* (H →L[ℂ] H))
    (b : V →ₗ[ℂ] H) (hb : ∀ v, IsSmoothVector I A (b v)) :
    V →ₗ[ℂ] DerivativeSmoothVectors I A :=
  (DerivativeSmoothVectors.toSmooth I A).symm.toLinearMap.comp
    (b.codRestrict (smoothVectors I A) hb)

set_option backward.isDefEq.respectTransparency true in
/-- The Frobenius map into the genuine carrier with its word-derivative topology. -/
def frobeniusSmoothMap :=
  liftToDerivativeSmoothVectors (n := n) (H := W) (V := V) R j
    (isSmoothVector_frobeniusClosureMap hgk hℓ)

@[simp]
theorem coe_toSmooth_frobeniusSmoothMap (v : V) :
    (DerivativeSmoothVectors.toSmooth I (E := W) R (frobeniusSmoothMap hgk hℓ v) : W) = j v := rfl

theorem frobeniusSmoothMap_injective (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) :
    Function.Injective (frobeniusSmoothMap hgk hℓ) := by
  intro v w h
  apply frobeniusClosureMap_injective hgk hℓ hirr h₀
  exact congrArg (fun y => (DerivativeSmoothVectors.toSmooth I (E := W) R y : W)) h

theorem frobeniusSmoothMap_compact (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
    frobeniusSmoothMap hgk hℓ (ρ k v) =
      DerivativeSmoothVectors.representation I (E := W) R (Unitary.toUnits k)
        (frobeniusSmoothMap hgk hℓ v) := by
  let k' : K := ⟨Unitary.toUnits k, k.2⟩
  apply (DerivativeSmoothVectors.toSmooth I (E := W) R).injective
  apply Subtype.ext
  apply Subtype.ext
  exact (representation_frobeniusHilbert_compact hgk hℓ k' v).symm

theorem frobeniusSmoothMap_lie (X : Mat) (v : V) :
    frobeniusSmoothMap hgk hℓ (π (1 ⊗ₜ X) v) =
      DerivativeSmoothVectors.operator I (E := W) R X (frobeniusSmoothMap hgk hℓ v) := by
  apply (DerivativeSmoothVectors.toSmooth I (E := W) R).injective
  apply Subtype.ext
  exact (lieDerivative_frobeniusClosureMap hgk hℓ X v).symm

theorem frobeniusSmoothMap_mem_kFinite (v : V) :
    frobeniusSmoothMap hgk hℓ v ∈ smoothHilbertKFinite ℝ n (H := W) R := by
  let r := smoothHilbertCompactRepresentation ℝ n (H := W) R
  change FiniteDimensional ℂ (FiniteVectors.orbitSpan r (frobeniusSmoothMap hgk hℓ v))
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hgk.1 v
  apply Submodule.finiteDimensional_of_le
    (S₂ := (FiniteVectors.orbitSpan ρ v).map (frobeniusSmoothMap hgk hℓ))
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨ρ k v, FiniteVectors.action_mem_orbitSpan ρ k v, ?_⟩
  exact frobeniusSmoothMap_compact hgk hℓ k v

end Langlands.Archimedean.RealPrincipalSeriesHilbert
