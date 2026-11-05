import Langlands.Representation.Plancherel.RationalUnramifiedDensity
import Langlands.Representation.Plancherel.RationalUnramifiedLocalDivisibilityStatement

/-! # Conditional cancellation in the actual unramified scalar algebra -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI

section RegularContinuity

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))

/-- Every element of the evaluation-generated regular scalar algebra is
continuous for the existing compact-open character topology. -/
theorem continuous_unramifiedRegularFunction (b : unramifiedRegularFunctions ν) :
    Continuous b.val := by
  refine Algebra.adjoin_induction (p := fun f _ => Continuous f)
    ?_ ?_ ?_ ?_ b.property
  · intro x hx
    obtain ⟨g, rfl⟩ := hx
    exact Units.continuous_val.comp
      ((continuous_eval_const g).comp continuous_subtype_val)
  · intro c
    exact continuous_const
  · intro x y hx hy hcx hcy
    exact hcx.add hcy
  · intro x y hx hy hcx hcy
    exact hcx.mul hcy

/-- An algebraic unit of the actual function algebra has no zero evaluation. -/
theorem unramifiedRegularFunction_isUnit_eval_ne_zero
    (b : unramifiedRegularFunctions ν) (hb : IsUnit b)
    (χ : unramifiedCharacters ν) : b.val χ ≠ 0 :=
  (hb.map ((Pi.evalRingHom (fun _ => ℂ) χ).comp
    (unramifiedRegularFunctions ν).val.toRingHom)).ne_zero

end RegularContinuity

section ActualCancellation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  (hdiv : RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u})

include hp hG hdiv

/-- Assuming the missing local hypersurface theorem, a factor meeting the open
region cancels from a scalar regular-numerator identity with continuous value. -/
theorem rationalUnramified_cancel_irreducible
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (p b a : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hpirr : Irreducible p) (hzero : ∃ χ ∈ U, p.val χ = 0)
    (f : U → ℂ) (hf : Continuous f)
    (hid : ∀ χ : U, (p * b).val χ.val * f χ = a.val χ.val) :
    ∃ c : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
      a = p * c ∧ ∀ χ : U, b.val χ.val * f χ = c.val χ.val := by
  obtain ⟨c, hc⟩ := hdiv G hp hG U p a hU hpirr hzero (by
    intro χ hχ hpχ
    have hi := hid ⟨χ, hχ⟩
    change (p.val χ * b.val χ) * f ⟨χ, hχ⟩ = a.val χ at hi
    rw [hpχ, zero_mul, zero_mul] at hi
    exact hi.symm)
  refine ⟨c, hc, ?_⟩
  have he : (fun χ : U => b.val χ.val * f χ) = (fun χ : U => c.val χ.val) := by
    apply Continuous.ext_on
      (rationalUnramifiedRegular_dense_nonzero_on_open G hp hG p hpirr.ne_zero hU)
      (((continuous_unramifiedRegularFunction _ b).comp continuous_subtype_val).mul hf)
      ((continuous_unramifiedRegularFunction _ c).comp continuous_subtype_val)
    intro χ hpχ
    apply mul_left_cancel₀ hpχ
    calc
      p.val χ.val * (b.val χ.val * f χ) = (p * b).val χ.val * f χ := by
        change _ = (p.val χ.val * b.val χ.val) * f χ
        exact (mul_assoc _ _ _).symm
      _ = a.val χ.val := hid χ
      _ = p.val χ.val * c.val χ.val := by rw [hc]; rfl
  exact fun χ => congrFun he χ

/-- One divisor of the original nonzero scalar denominator works for every
continuous scalar function with a regular numerator, and is nonzero at every
point of the open region. The denominator is chosen before the functions. -/
theorem rationalUnramified_uniform_scalar_denominator
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    ∃ d : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
      d ≠ 0 ∧ d ∣ b ∧ (∀ χ ∈ U, d.val χ ≠ 0) ∧
      ∀ (f : U → ℂ), Continuous f →
        ∀ a : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
          (∀ χ : U, b.val χ.val * f χ = a.val χ.val) →
          ∃ c : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
            ∀ χ : U, d.val χ.val * f χ = c.val χ.val := by
  classical
  let := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid G hp hG
  induction b using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hb rfl).elim
  | h₂ b hunit =>
      refine ⟨b, hb, dvd_rfl, ?_, ?_⟩
      · intro χ hχ
        exact unramifiedRegularFunction_isUnit_eval_ne_zero _ b hunit χ
      · intro f hf a hid
        exact ⟨a, hid⟩
  | h₃ b p hb0 hpprime ih =>
      obtain ⟨d, hd0, hdb, hdU, hd⟩ := ih hb0
      by_cases hpzero : ∃ χ ∈ U, p.val χ = 0
      · refine ⟨d, hd0, dvd_trans hdb (dvd_mul_left b p), hdU, ?_⟩
        intro f hf a hid
        obtain ⟨a', ha', hid'⟩ := rationalUnramified_cancel_irreducible
          G hp hG hdiv hU p b a hpprime.irreducible hpzero f hf hid
        exact hd f hf a' hid'
      · refine ⟨p * d, mul_ne_zero hpprime.ne_zero hd0,
          mul_dvd_mul_left p hdb, ?_, ?_⟩
        · intro χ hχ
          change p.val χ * d.val χ ≠ 0
          exact mul_ne_zero (fun he => hpzero ⟨χ, hχ, he⟩) (hdU χ hχ)
        · intro f hf a hid
          have hf' : Continuous (fun χ : U => p.val χ.val * f χ) :=
            ((continuous_unramifiedRegularFunction _ p).comp continuous_subtype_val).mul hf
          obtain ⟨c, hc⟩ := hd (fun χ : U => p.val χ.val * f χ) hf' a (by
            intro χ
            calc
              b.val χ.val * (p.val χ.val * f χ) =
                  (p * b).val χ.val * f χ := by
                change _ = (p.val χ.val * b.val χ.val) * f χ
                ac_rfl
              _ = a.val χ.val := hid χ)
          refine ⟨c, fun χ => ?_⟩
          calc
            (p * d).val χ.val * f χ = d.val χ.val * (p.val χ.val * f χ) := by
              change (p.val χ.val * d.val χ.val) * f χ = _
              ac_rfl
            _ = c.val χ.val := hc χ

/-- A scalar denominator chosen once for the open region and original
denominator, before any continuous function or numerator. -/
def rationalUnramifiedCancelledDenominator
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul) :=
  Classical.choose (rationalUnramified_uniform_scalar_denominator G hp hG hdiv hU b hb)

theorem rationalUnramifiedCancelledDenominator_ne_zero
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb ≠ 0 :=
  (Classical.choose_spec
    (rationalUnramified_uniform_scalar_denominator G hp hG hdiv hU b hb)).1

theorem rationalUnramifiedCancelledDenominator_dvd
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb ∣ b :=
  (Classical.choose_spec
    (rationalUnramified_uniform_scalar_denominator G hp hG hdiv hU b hb)).2.1

theorem rationalUnramifiedCancelledDenominator_eval_ne_zero
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) (χ : U) :
    (rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val ≠ 0 :=
  (Classical.choose_spec
    (rationalUnramified_uniform_scalar_denominator G hp hG hdiv hU b hb)).2.2.1 χ.val χ.property

theorem rationalUnramifiedCancelledDenominator_numerator
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    (f : U → ℂ) (hf : Continuous f)
    (a : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hid : ∀ χ : U, b.val χ.val * f χ = a.val χ.val) :
    ∃ c : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
      ∀ χ : U,
        (rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val * f χ =
          c.val χ.val :=
  (Classical.choose_spec
    (rationalUnramified_uniform_scalar_denominator G hp hG hdiv hU b hb)).2.2.2 f hf a hid

end ActualCancellation

end Langlands.Plancherel
