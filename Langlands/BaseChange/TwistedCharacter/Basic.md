# Generic twisted character distributions

This module supplies the generic part of `Langlands.BaseChange.TwistedCharacter`.
It works for a Hausdorff, locally compact, totally disconnected topological group `G`
and an admissible representation `ρ` on a complex vector space `V`, without requiring
finite dimension or irreducibility.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), II.1.3, printed pp. 56–57, and II.2.7, printed p. 67,
define the twisted character by the trace of `ρ(φ) ∘ A`. Our `twistedDistribution μ ρ hρ A`
extends that formula to any endomorphism `A` and any such group. It uses the existing
`Character.finiteRankIntegratedAction` and `FiniteRankEnd.trace`. Its composite has
finite rank because the integrated action does, regardless of the rank of `A`.
The measure `μ` is an explicit argument with the Borel, compact-finiteness and left
invariance hypotheses of the existing `Character.distribution`; no normalization is chosen.

`HasTwistedCharacterValue ρ hρ A g c` says that, for every Haar measure on the Borel
sigma-algebra of `G`, this twisted distribution has the existing `HasLocalValue` at
`g` with value `c`: on some open neighborhood of `g`, it evaluates each supported
Schwartz–Bruhat test function as `c` times its integral. It mirrors
`JacquetLanglands.HasCharacterValue`. The neighborhood may depend on the Haar measure,
while the complex value does not. This is a predicate defining what a value means;
it does not assert that values always exist. HL II.1.3, printed p. 57, distinguishes
the measure-dependent distribution from its measure-independent character values.

The seven lemmas below use the same group, vector space and admissibility
hypotheses as the definitions. The first three also use the explicit measure `μ`
with the Borel, compact-finiteness and left invariance hypotheses above. All scalar
parameters lie in `ℂ`. Only the last lemma assumes `FiniteDimensional ℂ V`.
They are derived consequences of the trace construction in HL II.1.3, printed
pp. 56–57, and II.2.7, printed p. 67, and of the existing Library integrated-action,
finite-rank trace and local-value interfaces. HL do not state these arbitrary-group,
arbitrary-endomorphism generalizations.

- `twistedDistribution_apply`: for every `A : Module.End ℂ V` and
  `f : SchwartzBruhat G`, the value `twistedDistribution μ ρ hρ A f` is
  `FiniteRankEnd.trace` of the finite-rank endomorphism `ρ(f) ∘ A`, where `ρ(f)`
  denotes `Hecke.integratedAction μ ρ hρ.1 f`. The finite-rank witness comes from
  `Character.finiteRankIntegratedAction` followed by `comp_right A`.
  This is the defining formula, so the Lean proof is reflexivity.

- `twistedDistribution_one`: taking the identity endomorphism gives equality of
  distributions
  `twistedDistribution μ ρ hρ 1 = Character.distribution μ ρ hρ`.
  The proof evaluates both distributions at each test function and identifies
  their finite-rank maps, since right composition with the identity does nothing.

- `twistedDistribution_smul`: for every scalar `a` and endomorphism `A`,
  `twistedDistribution μ ρ hρ (a • A) = a • twistedDistribution μ ρ hρ A`.
  Thus scaling the twisting endomorphism scales the entire distribution, including
  when `a = 0`. The proof moves the scalar through right composition and uses the
  complex linearity of `FiniteRankEnd.trace`.

- `hasTwistedCharacterValue_one_iff`: for every `g : G` and `c : ℂ`,
  `HasTwistedCharacterValue ρ hρ 1 g c ↔ HasCharacterValue ρ hρ g c`.
  In words, the identity-twisted local values are precisely the ordinary character
  values. The proof unfolds the two predicates and uses
  `twistedDistribution_one` under their universal Haar-measure quantifiers.

- `HasTwistedCharacterValue.unique`: for the same `ρ`, `hρ`, `A` and `g`, if
  `HasTwistedCharacterValue ρ hρ A g c` and
  `HasTwistedCharacterValue ρ hρ A g c'`, then `c = c'`.
  The proof instantiates both universal quantifiers with `Measure.haar` and
  applies the existing `HasLocalValue.unique`. It asserts uniqueness conditional
  on the two value predicates, without asserting existence.

- `HasTwistedCharacterValue.smul`: if
  `HasTwistedCharacterValue ρ hρ A g c`, then for every scalar `a`,
  `HasTwistedCharacterValue ρ hρ (a • A) g (a * c)`.
  For each Haar measure the proof keeps the open neighborhood witnessing the
  original value, applies `twistedDistribution_smul` to each test function
  supported there, and reassociates scalar multiplication. No nonzero condition
  on `a` is needed.

- `hasTwistedCharacterValue_trace`: with the additional hypothesis
  `FiniteDimensional ℂ V`, every endomorphism `A` and point `g₀ : G` satisfy
  `HasTwistedCharacterValue ρ hρ A g₀ (LinearMap.trace ℂ V (ρ g₀ ∘ₗ A))`.
  Thus in finite dimension the twisted character value exists everywhere and is
  the ordinary linear-algebra trace of `ρ(g₀) ∘ A`.
  The implemented proof adapts the existing `hasCharacterValue_trace` argument.
  Choose `b = Module.finBasis ℂ V` and intersect the finitely many fibers
  `{g | ρ g (b i) = ρ g₀ (b i)}`. Smoothness, supplied by `hρ.1`, makes each
  orbit-map fiber open, so their intersection is an open neighborhood of `g₀`.
  Equality on the basis implies `ρ g = ρ g₀` throughout this neighborhood.
  For every Haar measure `μ` and every test function `f` supported there, the proof
  applies basis coordinate functionals and `Hecke.integratedAction_dual` to obtain
  `Hecke.integratedAction μ ρ hρ.1 f = (∫ y, f y ∂μ) • ρ g₀`.
  Composing this identity on the right with `A`, replacing the finite-rank trace
  by the ambient trace using `FiniteRankEnd.trace_eq_ambient`, and using trace
  linearity gives the required local-value formula.

The uniqueness proof uses a Haar measure as a proof witness only. Neither definition
selects a measure. No new notion of distribution, integrated action, finite-rank trace,
or ordinary character value is introduced.

Source: Henniart–Lemaire (2011), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
II.1.3 and II.2.7 (printed pp. 56–57 and 66–67; PDF pp. 64–65 and 74–75).
