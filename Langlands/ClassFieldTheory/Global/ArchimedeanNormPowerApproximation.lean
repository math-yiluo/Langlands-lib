import Langlands.ClassFieldTheory.Global.ArchimedeanNormOneRadicals
import Langlands.Global.Arithmetic.ArchimedeanPowerApproximation

/-! # Archimedean approximation of norm-power pairs -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct NumberField.LiesOver

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global.AdelicFunctoriality LocalClassField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B S : Type u} [Field F] [Field B] [Algebra F B] [CommRing S] [Algebra F S]

/-- The scalar units in a tensor algebra through its right factor. -/
def scalarTensorUnit : Sˣ →* (B ⊗[F] S)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : S →ₐ[F] B ⊗[F] S).toMonoidHom

/-- The determinant norm of a scalar tensor unit is its power by the extension degree. -/
theorem tensorNormUnits_scalarTensorUnit [FiniteDimensional F B] (s : Sˣ) :
    tensorNormUnits F B S (scalarTensorUnit s) = s ^ Module.finrank F B :=
  tensorNormUnits_scalar s

/-- The two scalar images of a base field unit agree in the tensor algebra. -/
theorem leftTensorUnit_scalar {K : Type u} [Field K] [Algebra F K] (s : Fˣ) :
    leftTensorUnit (F := F) (L := K) (Units.map (algebraMap F B).toMonoidHom s) =
      scalarTensorUnit (F := F) (B := B) (Units.map (algebraMap F K).toMonoidHom s) := by
  apply Units.ext
  change algebraMap F B (s : F) ⊗ₜ[F] (1 : K) =
    (1 : B) ⊗ₜ[F] algebraMap F K (s : F)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

variable [NumberField F] [NumberField B]

/-- One global extension-field unit realizes the given power classes in all completion
tensors at infinite places. -/
theorem exists_approximateCompletionTensorUnits {n : ℕ} (hn : 0 < n)
    (b : (v : InfinitePlace F) → (B ⊗[F] v.Completion)ˣ) :
    ∃ t : Bˣ, ∀ v : InfinitePlace F, ∃ q : (B ⊗[F] v.Completion)ˣ,
      leftTensorUnit t = b v * q ^ n := by
  let x (w : InfinitePlace B) : w.Completionˣ :=
    archimedeanCompletionUnitsEquiv (w.comap (algebraMap F B))
      (b (w.comap (algebraMap F B))) ⟨w, ⟨rfl⟩⟩
  obtain ⟨t, ht⟩ := Global.exists_representsArchimedeanUnitPowers B hn x
  refine ⟨t, fun v => ?_⟩
  have hcoord (w : InfinitePlacesAbove B v) : ∃ q : w.1.Completionˣ,
      Units.map (algebraMap B w.1.Completion).toMonoidHom t =
        archimedeanCompletionUnitsEquiv v (b v) w * q ^ n := by
    have heq : x w.1 = archimedeanCompletionUnitsEquiv v (b v) w := by
      rcases w with ⟨w, hw⟩
      have := InfinitePlace.LiesOver.comap_eq w v
      subst v
      rfl
    obtain ⟨q, hq⟩ := ht w.1
    exact ⟨q, hq.trans (congrArg (· * q ^ n) heq)⟩
  choose q hq using hcoord
  let e := archimedeanCompletionUnitsEquiv (B := B) v
  refine ⟨e.symm q, e.injective ?_⟩
  funext w
  rw [map_mul, map_pow, e.apply_symm_apply]
  change archimedeanCompletionUnitsEquiv v (leftTensorUnit t) w =
    archimedeanCompletionUnitsEquiv v (b v) w * q w ^ n
  rw [archimedeanCompletionUnitsEquiv_left]
  exact hq w

/-- The global norm-power equation and a simultaneous realization of the local pairs,
with their power and norm ratios realized by the same local unit. -/
def RepresentsArchimedeanNormPowerPairs (n : ℕ) (b : Bˣ) (s : Fˣ)
    (b₀ : (v : InfinitePlace F) → (B ⊗[F] v.Completion)ˣ)
    (s₀ : (v : InfinitePlace F) → v.Completionˣ) : Prop :=
  normUnits F B b = s ^ n ∧
    ∀ v : InfinitePlace F, ∃ r : (B ⊗[F] v.Completion)ˣ,
      leftTensorUnit b = b₀ v * r ^ n ∧
      Units.map (algebraMap F v.Completion).toMonoidHom s = s₀ v * tensorNormUnits F B v.Completion r

private theorem normUnits_scalar (s : Fˣ) :
    normUnits F B (Units.map (algebraMap F B).toMonoidHom s) = s ^ Module.finrank F B := by
  apply Units.ext
  exact Algebra.norm_algebraMap _

/-- Coprime degree and exponent allow a global pair by a Bézout identity. -/
theorem exists_representsArchimedeanNormPowerPairs_of_coprime {n : ℕ} (hn : 0 < n)
    (hdeg : (Module.finrank F B).Coprime n)
    (b₀ : (v : InfinitePlace F) → (B ⊗[F] v.Completion)ˣ)
    (s₀ : (v : InfinitePlace F) → v.Completionˣ)
    (hN : ∀ v, tensorNormUnits F B v.Completion (b₀ v) = s₀ v ^ n) :
    ∃ (b : Bˣ) (s : Fˣ), RepresentsArchimedeanNormPowerPairs n b s b₀ s₀ := by
  let d := Module.finrank F B
  let a := Nat.gcdA d n
  let c := Nat.gcdB d n
  have hbez : (d : ℤ) * a + n * c = 1 := by
    have h := Nat.gcd_eq_gcd_ab d n
    rw [show d.gcd n = 1 from hdeg, Nat.cast_one] at h
    exact h.symm
  have hratio {A : Type u} [CommGroup A] (z : A) :
      z / (z ^ a) ^ d = (z ^ c) ^ n := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    nth_rw 1 [← zpow_one z]
    rw [div_eq_mul_inv, ← zpow_sub]
    congr 1
    rw [mul_comm a, mul_comm c]
    linarith only [hbez]
  obtain ⟨t, ht⟩ := exists_approximateCompletionTensorUnits hn b₀
  let T := normUnits F B t
  refine ⟨t / Units.map (algebraMap F B).toMonoidHom (T ^ a), T ^ c, ?_, ?_⟩
  · rw [map_div, normUnits_scalar]
    exact hratio T
  intro v
  obtain ⟨q, hq⟩ := ht v
  let N := tensorNormUnits F B v.Completion
  let f := Units.map (algebraMap F v.Completion).toMonoidHom
  let j := scalarTensorUnit (F := F) (B := B) (S := v.Completion)
  let h := s₀ v * N q
  have hh : f T = h ^ n := calc
    f T = N (leftTensorUnit t) := (tensorNormUnits_left (F := F) (L := v.Completion) t).symm
    _ = N (b₀ v * q ^ n) := congrArg N hq
    _ = h ^ n := by
      rw [map_mul, map_pow]
      change tensorNormUnits F B v.Completion (b₀ v) * N q ^ n = (s₀ v * N q) ^ n
      rw [hN v, mul_pow]
  refine ⟨q / j (h ^ a), ?_, ?_⟩
  · have hscalar : f (T ^ a) = (h ^ a) ^ n := by
      rw [map_zpow, hh, ← zpow_natCast, ← zpow_natCast, zpow_comm h]
    have hj : leftTensorUnit (Units.map (algebraMap F B).toMonoidHom (T ^ a)) = (j (h ^ a)) ^ n :=
      (leftTensorUnit_scalar (K := v.Completion) _).trans
        ((congrArg j hscalar).trans (map_pow j _ _))
    rw [map_div, hq, hj, div_pow, mul_div_assoc]
  · change f (T ^ c) = s₀ v * N (q / j (h ^ a))
    calc
      f (T ^ c) = (h ^ c) ^ n := by
        rw [map_zpow, hh, ← zpow_natCast, ← zpow_natCast, zpow_comm h]
      _ = h / (h ^ a) ^ d := (hratio h).symm
      _ = s₀ v * N (q / j (h ^ a)) := by
        have hscalar : N (j (h ^ a)) = (h ^ a) ^ d := tensorNormUnits_scalarTensorUnit _
        rw [map_div, hscalar, ← mul_div_assoc]

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro
