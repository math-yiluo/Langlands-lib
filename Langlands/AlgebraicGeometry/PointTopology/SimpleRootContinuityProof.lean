import Langlands.AlgebraicGeometry.PointTopology.SimpleRootContinuityStatement
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-! # Continuity of a simple root via the product-domain implicit function theorem -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Filter
open scoped Topology BigOperators

namespace Langlands.AlgebraicGeometry.PointTopology

private def monicFamily {K : Type u} [CommRing K] (n : ℕ) (c : Fin n → K) :
    Polynomial K :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ i.val

private theorem monicFamily_strict {K : Type u} [NontriviallyNormedField K]
    (n : ℕ) (z : (Fin n → K) × K) :
    ∃ D : ((Fin n → K) × K) →L[K] K,
      HasStrictFDerivAt (fun v => (monicFamily n v.1).eval v.2) D z := by
  classical
  have hi (i : Fin n) :
      ∃ Di : ((Fin n → K) × K) →L[K] K,
        HasStrictFDerivAt (fun v => v.1 i * v.2 ^ i.val) Di z := by
    exact ⟨_, ((hasStrictFDerivAt_apply (𝕜 := K) i z.1).comp z
      hasStrictFDerivAt_fst).mul
        ((hasStrictFDerivAt_snd (𝕜 := K) (p := z)).pow i.val)⟩
  choose Di hDi using hi
  have hsum := HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hDi i)
  have htotal :=
    ((hasStrictFDerivAt_snd (𝕜 := K) (p := z)).pow n).add hsum
  refine ⟨(n • z.2 ^ (n - 1)) • ContinuousLinearMap.snd K (Fin n → K) K +
    ∑ i, Di i, ?_⟩
  convert htotal using 1
  · funext v
    simp [monicFamily, Polynomial.eval_finsetSum]

private theorem monicFamily_derivative_continuous {K : Type u}
    [NontriviallyNormedField K] (n : ℕ) :
    Continuous (fun v : (Fin n → K) × K => (monicFamily n v.1).derivative.eval v.2) := by
  simp only [monicFamily, Polynomial.derivative_add, Polynomial.derivative_sum,
    Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X_pow,
    Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  fun_prop

/-- The local continuous simple-root branch, including local uniqueness and simplicity. -/
theorem monicSimpleRootContinuity : MonicSimpleRootContinuityStatement.{u} := by
  intro K _ _ n _hn
  dsimp only
  intro c a hroot hsimple
  change (monicFamily n c).eval a = 0 at hroot
  change (monicFamily n c).derivative.eval a ≠ 0 at hsimple
  let f : ((Fin n → K) × K) → K :=
    fun v => (monicFamily n v.1).eval v.2
  obtain ⟨D, hD⟩ := monicFamily_strict n (c, a)
  change HasStrictFDerivAt f D (c, a) at hD
  have hvertical :
      HasStrictFDerivAt (fun t => f (c, t))
        (D ∘L ContinuousLinearMap.inr K (Fin n → K) K) a := by
    convert hD.comp a
      ((hasStrictFDerivAt_const c a).prodMk (hasStrictFDerivAt_id a))
      using 1
    ext
    rfl
  have hvertical_eq :
      D ∘L ContinuousLinearMap.inr K (Fin n → K) K =
        (1 : K →L[K] K).smulRight ((monicFamily n c).derivative.eval a) :=
    hvertical.hasFDerivAt.unique ((monicFamily n c).hasFDerivAt a)
  have hinvertible : (D ∘L ContinuousLinearMap.inr K (Fin n → K) K).IsInvertible := by
    rw [hvertical_eq]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (1 : K →L[K] K).smulRight ((monicFamily n c).derivative.eval a)⁻¹)
    · ext
      simp [hsimple]
    · ext
      simp [hsimple]
  let ψ := hD.implicitFunctionOfProdDomain hinvertible
  have hψa : ψ c = a :=
    (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinvertible).self_of_nhds.mp rfl
  have hψcont : ContinuousAt ψ c := by
    exact (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hinvertible).continuousAt
  have hψroot : ∀ᶠ C in 𝓝 c, (monicFamily n C).eval (ψ C) = 0 := by
    have h := hD.eventually_apply_implicitFunctionOfProdDomain hinvertible
    change ∀ᶠ C in 𝓝 c,
      (monicFamily n C).eval (ψ C) = (monicFamily n c).eval a at h
    simpa only [hroot] using h
  have hψsimple : ∀ᶠ C in 𝓝 c, (monicFamily n C).derivative.eval (ψ C) ≠ 0 := by
    have hcont : ContinuousAt
        (fun C => (monicFamily n C).derivative.eval (ψ C)) c :=
      (monicFamily_derivative_continuous (K := K) n).continuousAt
        (x := (c, ψ c)) |>.comp
        (f := fun C : Fin n → K => (C, ψ C))
        ((continuousAt_id (x := c)).prodMk hψcont)
    exact hcont.eventually_ne (by simpa only [hψa] using hsimple)
  refine ⟨ψ, hψa, hψcont, hψroot.and hψsimple, ?_⟩
  have h := hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinvertible
  change ∀ᶠ v in 𝓝 (c, a),
    (monicFamily n v.1).eval v.2 = (monicFamily n c).eval a ↔ ψ v.1 = v.2 at h
  change ∀ᶠ v in 𝓝 (c, a),
    (monicFamily n v.1).eval v.2 = 0 ↔ ψ v.1 = v.2
  simpa only [hroot] using h

end Langlands.AlgebraicGeometry.PointTopology
