import Langlands.ClassField.Global.QuadraticTensorUnitConjugation

/-! # Archimedean norm-power approximation for a quadratic extension -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.GroupScheme.SU3Root LocalClassField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [Field B] [Algebra F B] [NumberField F] [NumberField B]

section Quadratic

variable [Algebra.IsQuadraticExtension F B]

private theorem exists_representsArchimedeanNormPowerPairs_of_quadratic_even
    {m : ℕ} (hm : 0 < 2 * m)
    (b₀ : (v : InfinitePlace F) → (B ⊗[F] v.Completion)ˣ)
    (s₀ : (v : InfinitePlace F) → v.Completionˣ)
    (hN : ∀ v, tensorNormUnits F B v.Completion (b₀ v) = s₀ v ^ (2 * m)) :
    ∃ (b : Bˣ) (s : Fˣ), RepresentsArchimedeanNormPowerPairs (2 * m) b s b₀ s₀ := by
  let j (v : InfinitePlace F) := scalarTensorUnit (F := F) (B := B) (S := v.Completion)
  let C (v : InfinitePlace F) := quadraticTensorUnitConjugation (F := F) (B := B) (S := v.Completion)
  let N (v : InfinitePlace F) := tensorNormUnits F B v.Completion
  have hscalar (v : InfinitePlace F) (s : v.Completionˣ) : N v (j v s) = s ^ 2 :=
    (tensorNormUnits_scalarTensorUnit (F := F) (B := B) s).trans
      (congrArg (s ^ ·) (Algebra.IsQuadraticExtension.finrank_eq_two F B))
  have hloc (v : InfinitePlace F) : ∃ t : (B ⊗[F] v.Completion)ˣ,
      b₀ v / (j v (s₀ v)) ^ m = t / C v t := by
    apply exists_archimedeanTensorUnit_div_conjugate v
    change N v (b₀ v / (j v (s₀ v)) ^ m) = 1
    rw [map_div, map_pow, hscalar, ← pow_mul]
    exact div_eq_one.mpr (hN v)
  choose t ht using hloc
  obtain ⟨a, ha⟩ := exists_approximateCompletionTensorUnits hm t
  obtain ⟨s, hs⟩ := Global.exists_representsArchimedeanUnitPowers F (n := 2) (by decide) s₀
  let fB := Units.map (algebraMap F B).toMonoidHom
  let aτ := Units.map (conjugation F B).toMonoidHom a
  let b := (fB s) ^ m * (a / aτ)
  refine ⟨b, s, ?_, ?_⟩
  · have hfield (s : Fˣ) : normUnits F B (fB s) = s ^ 2 := by
      apply Units.ext
      change Algebra.norm F (algebraMap F B (s : F)) = (s : F) ^ 2
      rw [Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]
    have hτ : normUnits F B aτ = normUnits F B a :=
      Units.ext (Algebra.norm_eq_of_algEquiv (conjugation F B) (a : B))
    change normUnits F B ((fB s) ^ m * (a / aτ)) = s ^ (2 * m)
    rw [map_mul, map_pow, hfield, map_div, hτ, div_self', mul_one, ← pow_mul]
  intro v
  let E := leftTensorUnit (F := F) (B := B) (L := v.Completion)
  let f := Units.map (algebraMap F v.Completion).toMonoidHom
  obtain ⟨q, hq⟩ := ha v
  obtain ⟨p, hp⟩ := hs v
  change E a = t v * q ^ (2 * m) at hq
  change f s = s₀ v * p ^ 2 at hp
  let r := j v p * (q / C v q)
  refine ⟨r, ?_, ?_⟩
  · have hsB : E (fB s) = j v (f s) := leftTensorUnit_scalar (K := v.Completion) s
    have hτ : E aτ = C v (E a) := (quadraticTensorUnitConjugation_left a).symm
    have hb : E b = (j v (f s)) ^ m * (E a / C v (E a)) := by
      change E ((fB s) ^ m * (a / aτ)) = _
      rw [map_mul, map_pow, map_div, hsB, hτ]
    have ht' : b₀ v = (j v (s₀ v)) ^ m * (t v / C v (t v)) :=
      div_eq_iff_eq_mul'.mp (ht v)
    have hq' : E a / C v (E a) = (t v / C v (t v)) * (q / C v q) ^ (2 * m) := by
      rw [hq, map_mul, map_pow, div_pow, div_mul_div_comm]
    have hp' : (j v (f s)) ^ m = (j v (s₀ v)) ^ m * (j v p) ^ (2 * m) := by
      rw [hp, map_mul, map_pow, mul_pow, ← pow_mul]
    change E b = b₀ v * r ^ (2 * m)
    rw [hb, hq', hp', ht', show r ^ (2 * m) = _ from mul_pow _ _ _]
    exact mul_mul_mul_comm _ _ _ _
  · have hτ : N v (C v q) = N v q := tensorNormUnits_quadraticTensorUnitConjugation q
    have hr : N v r = p ^ 2 := by
      change N v (j v p * (q / C v q)) = p ^ 2
      rw [map_mul, hscalar, map_div, hτ, div_self', mul_one]
    exact hp.trans (congrArg (s₀ v * ·) hr.symm)

end Quadratic

/-- Simultaneous archimedean approximation for all pairs obeying the norm-power equation. -/
def ArchimedeanNormPowerApproximationStatement (F B : Type u) [Field F] [Field B]
    [Algebra F B] [NumberField F] [NumberField B] (n : ℕ) : Prop :=
  ∀ (b₀ : (v : InfinitePlace F) → (B ⊗[F] v.Completion)ˣ)
    (s₀ : (v : InfinitePlace F) → v.Completionˣ),
    (∀ v, tensorNormUnits F B v.Completion (b₀ v) = s₀ v ^ n) →
    ∃ (b : Bˣ) (s : Fˣ), RepresentsArchimedeanNormPowerPairs n b s b₀ s₀

/-- A positive power admits simultaneous approximation for quadratic degree or
degree coprime to the exponent. -/
theorem archimedeanNormPowerApproximation {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n) :
    ArchimedeanNormPowerApproximationStatement F B n := by
  intro b₀ s₀ hN
  rcases hdeg with hdeg | hdeg
  · let : Algebra.IsQuadraticExtension F B := { finrank_eq_two' := hdeg }
    by_cases hodd : Odd n
    · exact exists_representsArchimedeanNormPowerPairs_of_coprime hn
        (hdeg.symm ▸ hodd.coprime_two_left) b₀ s₀ hN
    · have heven : Even n := Nat.not_odd_iff_even.mp hodd
      obtain ⟨m, rfl⟩ := heven.two_dvd
      exact exists_representsArchimedeanNormPowerPairs_of_quadratic_even hn b₀ s₀ hN
  · exact exists_representsArchimedeanNormPowerPairs_of_coprime hn hdeg b₀ s₀ hN

end Langlands.ClassField.Global.TensorUnitShapiro
