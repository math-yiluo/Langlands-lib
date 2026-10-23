import Langlands.Representation.Shahidi.IntertwiningPadic
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.IntegralSubgroup
import Langlands.LocalField.Normalization.Definitions

/-!
# Convergence and rational continuation of Shahidi's intertwining operator

The two analytic assertions of Shahidi (1984), page 72, about the p-adic operator (0.1)
`A(s, π, w_{m,n}) f(g) = ∫_{U'} f(w_{m,n} u' g) du'`: it converges for `Re s ≫ 0`, and as a
function of `s` it continues to a rational function of `q^{-s}`. These are proposition
definitions; neither assertion is proved or assumed here.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi GeneralLinear MeasureTheory HarmonicAnalysis SmoothWeakIntegral
  RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The maximal compact subgroup `K_r = GL_r(O_F)` of `GL_r(F)`, for the integer ring of
the specified valuation. -/
abbrev shahidiMaximalCompact (r : ℕ) : Subgroup (GeneralLinear r F.Carrier) :=
  GeneralLinearGroup.integralSubgroup (Fin r) T.Integers

section Families

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂)

/-- A flat family `s ↦ f_s ∈ I(s, π₁ ⊗ π₂)`: the restriction of `f_s` to `K_{m+n}` does
not depend on `s`. -/
def IsShahidiFlatFamily (f : ∀ s : ℂ, T.ShahidiSourceSpace hm hn s π₁ π₂) : Prop :=
  ∀ (s t : ℂ) (k : GeneralLinear (m + n) F.Carrier), k ∈ T.shahidiMaximalCompact (m + n) →
    T.shahidiSourceEval hm hn s π₁ π₂ (f s) k = T.shahidiSourceEval hm hn t π₁ π₂ (f t) k

variable [MeasurableSpace F.Carrier]

/-- The scalar function `s ↦ ∫_{U'} ℓ(f_s(w_{m,n} u' g)) du'` of a family `f`, for a smooth
functional `ℓ` of `π₁ ⊗ π₂`. Where `f_s` lies in the convergence domain, this is
`ℓ(A(s, π, w_{m,n}) f_s(g))` read through the flip `V₂ ⊗ V₁ ≃ V₁ ⊗ V₂`
(`shahidiIntertwiningCoefficient_eq`). -/
def shahidiIntertwiningCoefficient (μ : Measure (Matrix (Fin n) (Fin m) F.Carrier))
    (f : ∀ s : ℂ, T.ShahidiSourceSpace hm hn s π₁ π₂) (g : GeneralLinear (m + n) F.Carrier) :
    letI := T.topology
    SmoothDual (pairRepresentation hm hn π₁ π₂) → ℂ → ℂ :=
  fun ℓ s => ∫ a, ℓ.val (T.shahidiSourceEval hm hn s π₁ π₂ (f s)
    (blockWeyl m n F.Carrier * intertwiningUnipotent m n F.Carrier a * g)) ∂μ

variable [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]
  {μ : Measure (Matrix (Fin n) (Fin m) F.Carrier)} [μ.IsAddLeftInvariant]
  (hμ : IsModulusScaling hm hn T.shahidiAbsoluteValue μ) {π₁ π₂}

/-- On the convergence domain, the coefficient is the pairing of `ℓ` with the value of the
operator `shahidiIntertwining`. -/
theorem shahidiIntertwiningCoefficient_eq :
    letI := T.topology
    letI := T.leviTopologicalGroup (twoBlocks m n hm hn)
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (f : ∀ s : ℂ, T.ShahidiSourceSpace hm hn s π₁ π₂)
      (g : GeneralLinear (m + n) F.Carrier) (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂))
      (s : ℂ) (hs : f s ∈ T.shahidiSourceDomain hm hn s π₁ π₂ μ),
      T.shahidiIntertwiningCoefficient hm hn π₁ π₂ μ f g ℓ s =
        ℓ.val (pairFlip.symm (T.shahidiTargetEval hm hn s π₁ π₂
          (T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂ ⟨f s, hs⟩) g)) := by
  let := T.topology
  intro hπ₁ hπ₂ f g ℓ s hs
  exact (T.shahidiIntertwining_eval hm hn s hμ hπ₁ hπ₂ ⟨f s, hs⟩ g ℓ).symm

end Families

section Statements

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- Shahidi (1984), page 72: for irreducible admissible `π₁`, `π₂`, the integral (0.1)
converges on all of `I(s, π₁ ⊗ π₂)` for `Re s` large. The measure on `U' ≅ M_{n×m}(F)` is
the product of an arbitrary additive Haar measure on `F`; the domain is the published
weak-integral convergence domain. -/
def ShahidiIntertwiningConvergenceStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  ∀ ν : AdditiveHaarMeasure F.Carrier,
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂),
    IsAdmissible π₁ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear m F.Carrier)) π₁.asModule →
    IsAdmissible π₂ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π₂.asModule →
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      T.shahidiSourceDomain hm hn s π₁ π₂ (rectangularMeasure ν n m) = ⊤

/-- Shahidi (1984), page 72: for irreducible admissible `π₁`, `π₂` and a flat family
`f_s ∈ I(s, π₁ ⊗ π₂)`, the integral (0.1) at `f_s` converges for `Re s` large, and for every
`k ∈ K_{m+n}` and every smooth functional `ℓ`, `s ↦ ℓ(A(s, π, w_{m,n}) f_s(k))` agrees on a
right half-plane with a rational function of `q^{-s}`, `q` the residue cardinality. -/
def ShahidiIntertwiningRationalityStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  ∀ ν : AdditiveHaarMeasure F.Carrier,
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂),
    IsAdmissible π₁ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear m F.Carrier)) π₁.asModule →
    IsAdmissible π₂ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π₂.asModule →
    ∀ f : (∀ s : ℂ, T.ShahidiSourceSpace hm hn s π₁ π₂), T.IsShahidiFlatFamily hm hn π₁ π₂ f →
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        f s ∈ T.shahidiSourceDomain hm hn s π₁ π₂ (rectangularMeasure ν n m)) ∧
      ∀ k ∈ T.shahidiMaximalCompact (m + n), ∀ ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂),
        ∃ R : RatFunc ℂ, HasRationalContinuation T.residueCardinality
          (T.shahidiIntertwiningCoefficient hm hn π₁ π₂ (rectangularMeasure ν n m) f k ℓ) R

end Statements

end Langlands.PadicField.TopologicalData
