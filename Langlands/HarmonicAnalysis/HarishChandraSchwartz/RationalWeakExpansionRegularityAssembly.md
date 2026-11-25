# Corollary V.2.3 from three named inputs

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularityAssembly`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and status

This module reduces the regularity target `WeightedCRegularityBorelStatement` (module
`RationalWeakExpansionTargets`; Waldspurger, Corollary V.2.3) to three named inputs, one for each
analytic ingredient of the source's proof. Each input is stated for one Weyl index, that is, for
one normalizer lift `n` with `s·M ⊆ M'`, its density packages `PG`, `PM` and their common compact
normalization `hN`:

1. `CDomainInteriorNonemptyStatement` (module `RationalWeakExpansionJointDomain`): the joint
   convergence domain of the c-family has nonempty interior.
2. `WeightedCContinuationPolesStatement` (this module): the weighted family has a rational
   continuation on its domain, together with a unitary pole presentation.
3. `WeightedCUnitaryBoundStatement` (this module): every such continuation satisfies the
   cleared bound at all unitary characters.

- **None of the three inputs is proved** here or anywhere in the Library.
- `WeightedCRegularityFromInputsStatement` is the implication from the three inputs (for every
  `s`) to `WeightedCRegularityBorelStatement`. It is proved by `weightedCRegularityFromInputs`.
- So `WeightedCRegularityBorelStatement` is **not proved** by this module. The module does not use
  or prove `WeightedWeakExpansionStatement`, `WeightedCDecompositionBorelStatement` or
  `WeightedPacketIdentityStatement`.

## Data and notation

The data are those of `RationalWeightedCPoleCancellation` (see its Markdown, "Inputs and
conclusion"), plus the split component `sc` of the Levi scheme `M₀` of `M = M_I` (`hs`), its
rational points `C_M`, and a Haar measure `μ` on `M(F)/C_M`.

- `M₀` is the Levi scheme of `M`. `Φ : X(M₀) ≃ X(M(F))` is the unramified character transport
  along `leviRationalPointHomeomorph`.
- `D₀ = cWeightedDomain …` is the published domain of the weighted family.
- `Ω = Φ⁻¹(interior D₀)`.
- `A` on `Ω` is the published `weightedCompactFamily` (`c̃_{P'|P}(s, ·)` on the fixed compact
  pictures) evaluated at the transported parameter.
- `Wₛ` is the lower compact picture, the target of `A`.

Every new definition binds `[BorelSpace (M(F)/C_M)]` explicitly. Its premise
"`π` is square integrable modulo `C_M`" is `IsSquareIntegrableModCentralSubgroup` for `μ` on that
Borel quotient. "`K` is special" is `IsSpecialVertexCompact ν hi K`. Elaborated-signature probe:
the two input statements, the
reduction statement and its proof each have exactly one `BorelSpace` binder.

## The inputs

**Definition `WeightedCContinuationPolesStatement`.** If `π` is square integrable modulo `C_M`
and `K` is special, then two things exist:

- a `RationalOperatorContinuationData Ω A`: one regular denominator `a` nonvanishing at every
  point of `Ω`, and one global polynomial numerator `P` with `P = a • A` on `Ω`;
- a `RationalOperatorPolePresentation M₀ a P`: a second regular denominator `b`, factored as a
  finite product of powers of unit-circle basis-coordinate factors `x_B − c` (`|c| = 1`) times a
  remainder vanishing at no unitary character, and a global polynomial numerator `Q` with
  `a • Q = b • P` on all of `X(M₀)`.

In words: `c̃_{P'|P}(s, ·)` is rational, and its unitary poles lie on finitely many unit-circle
hyperplanes `z(λ) = c` for primitive lattice vectors `λ`.

**Definition `WeightedCUnitaryBoundStatement`.** Assume that `π` is square integrable modulo
`C_M`, that `K` is special and that the interior of `D₀` is nonempty. Then there are a complex
normed space `E` (in universe `max u uV`) and a linear equivalence `e : Wₛ ≃ E` with the
following property. Every `RationalOperatorContinuationData Ω A`, say with denominator `a` and
numerator `P`, satisfies `HasClearedUnitaryBound`: for each source vector `v` there is `C ≥ 0`
with `‖e (P(z) v)‖ ≤ C ‖a(z)‖` at every unitary `z`. The premise on the interior is needed: if
`Ω` were empty, every pair `(a, P)` would be continuation data and no bound could hold.

## The proved reduction

**Definition `WeightedCRegularityFromInputsStatement`.** It has the explicit data of
`WeightedCRegularityBorelStatement`: the ambient and Levi data, `K` with compactness `hK` and
Iwasawa pair `hPK`, `π`, `PG`, `sc`, `hs`, `μ`, the representatives `Rep` and the family of lower
density packages `PMf`. Its body is: if for every Weyl index `s` the three inputs hold (inputs 2
and 3 for every common compact normalization of `PG` and `PMf s`), then
`WeightedCRegularityBorelStatement` holds for the same data and Borel instance.

**Theorem `weightedCRegularityFromInputs`.** Proof as implemented. Fix the target's premises:
square integrability, properness of `I'` (unused), special `K`, the source normalization `hN`
and `s`. Then:

1. The published `cWeightedDomain_interior_nonempty_of_cDomain` (input 1 with square
   integrability, special `K` and `hPK`) gives the nonempty interior of `D₀`.
2. Input 2 gives continuation data `p` and a pole presentation `q`.
3. Input 3 gives `e` and the bound for `p`.
4. The published `weightedCExtensionFromPoles e` (module `RationalWeightedCPoleCancellation`)
   turns the interior, `p`, `q` and the bound into `Nonempty (WeightedCExtension … (hN s))`.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).

The proof of Corollary V.2.3 (printed p.294) has three ingredients, which match the three inputs.

- **Pole structure.** "Il résulte des définitions et de IV.1 (12) qu'il existe un polynôme `Q`
  … de la forme `Q(λ) = ∏_α ⟨λ, α̌⟩^{n(α)}` … tel que l'application
  `λ ↦ Q(λ) µ^G(ω ⊗ χ_λ) µ^{M′}(s(ω ⊗ χ_λ))^{-1} c_{P′|P}(s, ω ⊗ χ_λ)` est régulière en `λ = 0`."
  The source puts the unitary poles near each `ω` on root hyperplanes. Input 2 asks for one global
  presentation whose unitary poles lie on unit-circle basis-coordinate hyperplanes. This is the
  form the Library's cancellation theorem (`RationalUnitaryPoleFactorization`) uses. The rational
  continuation in input 2 is IV.1 (rationality of the intertwining integrals) together with V.2.1
  (rationality of the densities).
- **Norm identity.** Equation (1) of the proof, from Lemma V.2.2 (printed pp.293–294): on the
  regular unitary locus, `‖C(λ)ψ‖² = c(G|M)² c(M′|s·M)^{-2} |Q(λ)|² µ^G(ω⊗χ_λ) µ^{M′}(s(ω⊗χ_λ))^{-1} ‖ψ‖²`.
  The norms on the fixed compact pictures do not depend on `λ`. The density ratio is the regular
  product `∏ µ_α`. With `Q = 1`, this bounds `c̃` on a dense set of unitary characters. The
  cleared form of that bound on all unitary characters is input 3; the Library's
  `hasClearedUnitaryBound_of_dense` passes from the dense form to the cleared form.
- **Pole cancellation.** The minimality argument on `n(α)` is replaced by the published
  `weightedCExtensionFromPoles` (derived; see its Markdown).

Input 1 is not an ingredient of the source's proof. It is the field `interior_nonempty` of the
Library's `WeightedCExtension`, which makes the extension agree with the actual integrals on an
open set (see `RationalWeakExpansionJointDomain`).

The reduction is **derived**: the source does not separate these inputs, and the global form of
input 2 is a reformulation of its local statement.

## Imports

`RationalWeightedCPoleCancellation` (`weightedCExtensionFromPoles`, and through it the target
module) and `RationalWeakExpansionJointDomain` (`CDomainInteriorNonemptyStatement`,
`cWeightedDomain_interior_nonempty_of_cDomain`). No axioms, no `sorry`.
