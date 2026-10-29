# Support on the compatible torus from fiber invariance: proof

Author: Worker 885.

This module proves `Langlands.Whittaker.bruhatCompatibleSupport.{uF}`, whose type is
exactly the published proposition
`Langlands.Whittaker.BruhatCompatibleSupportStatement.{uF}` of
`Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement`. The statement
module and everything it imports are used unchanged. Besides the statement module, the
proof imports only the published modules

- `Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof` (covariance of
  the character average under the fiber action),
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` (surjectivity
  of the character average), and
- `Langlands.Representation.Twist.ContinuousCharacterProof` (open kernels of continuous
  complex characters).

## What is proved

For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical normed
field structure, every `n : ℕ` (including `n = 0`), every unitary additive character
`ψ` and every permutation `w` of `Fin (n + 1)`, with `U = upperUnipotent (n + 1) F.Carrier`
carrying `borel U`, `P = permutationUnipotentPlus (n + 1) F.Carrier w`,
`H = Fin (n + 1) → F.Carrierˣ` and `M = U × (H × U)`: for every Haar measure `μ` on `U`
that is s-finite and right invariant and every algebraic distribution
`τ : Distribution H`, if

    Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α)
      = Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ α

for all `u : P` and `α : SchwartzBruhat M`, then
`τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)`, that is, `τ f = 0` for every test
function `f` on `H` vanishing on the compatible torus. No hypothesis is added; in
particular `τ` is an arbitrary complex-linear functional, with no continuity.

## Declarations

The auxiliary declarations defined here are in `Langlands.Whittaker`. The
shared character lemma below retains its existing `Langlands.RankinSelberg` name.

- `BruhatCompatibleSupport.clopenCutoff hV f`: for a clopen set `V` of a topological space
  `X` and `f : SchwartzBruhat X`, the test function `x ↦ 1_V(x) * f x`, built from
  Mathlib's `LocallyConstant.charFn ℂ hV`. It is locally constant as a product of
  locally constant functions and has compact support because `f` has. The two evaluation
  lemmas `clopenCutoff_apply_of_mem` and `clopenCutoff_apply_of_notMem` give `f x` on `V`
  and `0` off `V`.
- `BruhatCompatibleSupport.apply_eq_zero_of_local τ f hloc`: finite local-to-global
  vanishing for an algebraic distribution `τ : Distribution X` on any topological space.
  If every `x` with `f x ≠ 0` lies in a clopen set `V` such that `τ g = 0` for every test
  function `g` whose nonzero values all lie in `V`, then `τ f = 0`.
- `Langlands.RankinSelberg.isLocallyConstant_of_continuous_complex_character θ hθ`,
  imported from `Langlands.Representation.Twist.ContinuousCharacterProof`: a
  continuous homomorphism `θ : G →* ℂˣ` on a nonarchimedean topological group has
  locally constant complex values `g ↦ (θ g : ℂ)`. Integration moved this existing
  declaration from the rank-one Jacquet functional proof and removed the equivalent
  helper formerly named `BruhatCompatibleSupport.isLocallyConstant_coe_of_continuous`.
- `bruhatCompatibleSupport_of_covariance hcov`: the support statement derived from the
  published covariance proposition `BruhatFiberCharacterCovarianceStatement.{uF}`, taken
  as a hypothesis.
- `bruhatCompatibleSupport : BruhatCompatibleSupportStatement.{uF}`, the target, equal to
  `bruhatCompatibleSupport_of_covariance bruhatFiberCharacterCovariance`, where
  `bruhatFiberCharacterCovariance` is the published proof of the covariance proposition.

## The implemented argument

Write `χ = standardCharacterContinuous ψ n`, `β_α = SchwartzBruhat.characterAverage χ μ α`,
`α^u = Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α`,
`ι` for the inclusion `P ≤ U` (`permutationUnipotentPlus_le_upperUnipotent`), `p_w` for
`permutation (n + 1) F.Carrier w` and `s(d) = p_w * Iwasawa.diagonalUnits d`.

0. **Setup.** After introducing the binders of the proposition (and the instances
   `borel U` and `BorelSpace U` exactly as the statement installs them), the proof records
   the published structure of `U`: topological group, Hausdorff, locally compact and
   nonarchimedean (`F.canonicalUpperUnipotentTopologicalGroup`, `…T2Space`,
   `…LocallyCompactSpace`, `…Nonarchimedean`, each at `n + 1`).

1. **Surjectivity.** The published theorem
   `SchwartzBruhat.characterAverageSurjective : CharacterAverageSurjectiveStatement`,
   applied to `G = U`, `Y = H`, `χ` and `μ` (which is Haar and s-finite), says that every
   test function `g` on `H` is `β_α` for some `α : SchwartzBruhat M`.

2. **Vanishing where a defect is a constant different from one.** Let `u : P`, `c ≠ 1`
   and let `g` be a test function on `H` such that
   `compatibilityDefect ψ n w (ι u) d = c` whenever `g d ≠ 0`. Write `g = β_α` (step 1).
   The covariance proposition, applied with the same `p, F, n, ψ, w, μ` (its
   hypotheses `IsFiniteMeasureOnCompacts μ` and `IsMulLeftInvariant μ` come from the
   Haar property), gives for every `d`

       β_{α^u} d = (compatibilityDefect ψ n w (ι u) d)⁻¹ * β_α d.

   At points with `β_α d = 0` both sides vanish; at the other points the defect is `c`.
   Hence `β_{α^u} = c⁻¹ • β_α` as test functions. The invariance hypothesis, read through
   `Distribution.characterAverageDual_apply`, is `τ β_{α^u} = τ β_α`; by linearity of
   `τ` this becomes `c⁻¹ * τ β_α = τ β_α`, that is `(c⁻¹ - 1) * τ β_α = 0`. Since
   `c ≠ 1`, also `c⁻¹ ≠ 1`, so `τ g = τ β_α = 0`.

3. **A locally constant defect at each point off the torus.** Let `f` vanish on
   `compatibleTorus ψ n w` (`Distribution.mem_supportedOn_iff`) and let `f d₀ ≠ 0`. Then
   `d₀` is not in the compatible torus, and the published `mem_compatibleTorus_iff_defect`
   gives `v : U` with `p_w * v * p_w⁻¹ ∈ U` and `compatibilityDefect ψ n w v d₀ ≠ 1`. By
   `mem_permutationUnipotentPlus_iff`, `v` lies in `P`; call this element `u : P`, so
   `ι u = v`. The published `compatibilityDefect_eq_div` writes, for every `d`,

       compatibilityDefect ψ n w v d = (χ (s(d) * v * s(d)⁻¹) : ℂ) / (χ v : ℂ),

   with `s(d) * v * s(d)⁻¹` bundled in `U` by `monomial_conj_mem_upperUnipotent`. The map
   `d ↦ s(d) * v * s(d)⁻¹` from `H` to `U` is continuous (`continuous_diagonalUnits`,
   continuity of multiplication and inversion in `GL_{n+1}`, and `Continuous.subtype_mk`).
   The complex values of `χ` are locally constant on `U` by
   `RankinSelberg.isLocallyConstant_of_continuous_complex_character`: the published
   `isOpen_ker_of_continuous_complex_character` makes the kernel of `χ` open, and on the
   open neighbourhood `g * ker χ` of each `g` the value of `χ` is `χ g`. Composing a
   locally constant function with a continuous map and then with division by the constant
   `χ v` gives that `d ↦ compatibilityDefect ψ n w v d` is locally constant on `H`.
   Therefore its level set
   `V = {d | compatibilityDefect ψ n w v d = compatibilityDefect ψ n w v d₀}` is clopen
   (`IsLocallyConstant.isClopen_fiber`) and contains `d₀`. Every test function `g` whose
   nonzero values lie in `V` satisfies the hypothesis of step 2 with
   `c = compatibilityDefect ψ n w v d₀ ≠ 1`, hence `τ g = 0`.

4. **Finite clopen cover.** `apply_eq_zero_of_local`, fed with the sets `V` of step 3,
   gives `τ f = 0`. Its proof chooses such a `V` for every point of the support of `f`.
   The support of a test function is compact (`Hecke.TestFunction.isCompact_support`), so
   `IsCompact.elim_nhds_subcover'` gives a finite set `t` of support points whose sets
   cover the support. Induction on finite sets `s` then proves: every test function `g`
   whose nonzero values lie in `⋃ x ∈ s, V x` satisfies `τ g = 0`. For `s = ∅`, `g = 0`.
   For `insert x s`, split `g = clopenCutoff (V x) g + (g - clopenCutoff (V x) g)`; the
   first summand has nonzero values only in `V x`, so `τ` kills it by the choice of
   `V x`; the second vanishes on `V x` and wherever `g` vanishes, so its nonzero values
   lie in `⋃ y ∈ s, V y` and the induction hypothesis applies. Linearity of `τ` finishes
   the step. Only finitely many test functions are ever fed to `τ`; no integral of `τ`
   and no continuity of `τ` occurs.

## Relation to Shalika's proof

The proposition is the support assertion of Proposition 1.13 of J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193, printed
p.177, registered as `shalika-1974-multiplicity-one`, in the internal formulation
explained in the statement's Markdown. Shalika computes
`β_{α^u}(h) = δ(h) β_α(h)` with `δ(h) = χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u)`, concludes
`τ((δ − 1)β) = 0` for all `β` (the printed "(γ − 1)β" is a misprint for "(δ − 1)β") and
then reads off the support. In the present notation Shalika's `δ` is the inverse
`(compatibilityDefect ψ n w (ι u))⁻¹`, which is the factor supplied by the published
covariance theorem, so no passage to `u⁻¹` is needed. The last inference, which the
source leaves implicit, is made explicit here: instead of dividing by `δ − 1`, the proof
restricts to clopen level sets of the defect, where `δ` is a constant different from one
(step 2), and glues finitely many of them over the compact support of `f` (steps 3 and
4). Local constancy of the defect, which the source uses tacitly, is proved from the
open kernel of the continuous standard character on the nonarchimedean group `U`. These
steps are internal arguments, not quotations of the source.

## Hypotheses that are not needed

- No continuity, boundedness or positivity of `τ`; only finite linearity.
- No countability: `SFinite μ` is a hypothesis of the statement and is passed on to the
  covariance and surjectivity theorems.
- Right invariance of `μ` is used only through the covariance theorem; the Haar property
  supplies its other two instance hypotheses and the hypotheses of the surjectivity
  theorem.
- No case distinction on `n`: the rank-one case `n = 0` is covered by the same argument.

The proof uses no `sorry` and no new axiom.

## Provenance

The proof was written by Worker 885 alone. It uses the published covariance proof of
Worker 884 (`bruhatFiberCharacterCovariance`) and the published surjectivity proof
(`characterAverageSurjective`) as imported theorems, by Lean name, and reuses no draft by
another author. The finite clopen-cover induction follows the pattern of the private
lemma `mem_of_local_cutoffs` of `Langlands.HarmonicAnalysis.Distribution.LocalizationProof`,
rewritten here for an algebraic distribution. Worker 1005, collaborator on this task,
independently drafted an equivalent localization lemma
(`supportedOn_of_local_clopen_vanishing`, task draft revision 1); this module does not use
that draft.
