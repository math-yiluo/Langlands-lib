# Laumon's `s(V)` and the transported Swan exponent

Laumon's numerical statement is written in the Library with the Swan predicate
`Langlands.Henniart.LocalNumerical.LadicHasSwan K Ω ℓ ι ρ s` of
`Langlands.Correspondence.HenniartLadicStatement`: a positive-rank irreducible ℓ-adic Galois
class `ρ` (`IrreducibleLadicClass`) has Swan exponent `s` when its image under
`ladicWeilTransport` (restriction to the local Weil group, then extension of scalars to `ℂ`
along `ι : E →+* ℂ`, `E = PadicAlgCl ℓ`) is the class of a continuous irreducible complex Weil
class `σ` with `HasWeilSwan K Ω σ s`. There `HasWeilSwan` is `a − (k + 1) = s`, in `ℕ`, for an
Artin exponent `a` given by `HasArtinConductor` at a finite inertia presentation with surjective
inertia restriction, and `k + 1` is the rank. Laumon (1987) works with the slope-weighted Swan
conductor `s(V)` of (2.1.2.5), p. 152, which is `ladicSwan` of
`Langlands.Correspondence.Laumon.Slopes` for `G`-modules (`f = MonoidHom.id`).

This module carries out the row `SwanComparison` of §4.6 of the [design note for Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md) (bridge (b3), class side),
with its statement under the name of the row.

## `TransportedLadicSwanStatement`

For a nonarchimedean local field `K` of either characteristic with separable closure `Ω`, a prime
`ℓ` different from the residue characteristic (`((ℓ : ℕ) : 𝓀[K]) ≠ 0`), every ring homomorphism
`ι : E →+* ℂ`, every `k : ℕ`, every `ρ : IrreducibleLadicClass K Ω ℓ (k + 1)` and every `s : ℕ`:

1. `LadicHasSwan K Ω ℓ ι ρ s` holds if and only if some representative `A` of `ρ` (an `A` with
   `classOf A = ladicClassForget K Ω ℓ ρ`) has `ladicSwan (MonoidHom.id _) A = s`;
2. it holds if and only if every representative has `ladicSwan (MonoidHom.id _) A = s`;
3. it does not depend on `ι`: `LadicHasSwan K Ω ℓ ι' ρ s ↔ LadicHasSwan K Ω ℓ ι ρ s` for every
   `ι'`;
4. it is invariant under unramified twists: for every `χ` in `ladicUnramifiedCharacters K Ω ℓ`,
   `LadicHasSwan K Ω ℓ ι (ladicUnramifiedTwist K Ω ℓ k χ ρ) s ↔ LadicHasSwan K Ω ℓ ι ρ s`.

The unramified case is included: if inertia has a nonzero fixed vector on an irreducible `V`,
the fixed space is stable under the whole Galois group (inertia is normal), so it is `V`; the
Artin exponent is then `0`, natural subtraction gives Swan exponent `0`, and `s(V) = 0` because
wild inertia acts trivially. Clauses 3 and 4 follow from 1 and 2: `s(V)` involves neither `ι`
nor a twist by a character trivial on inertia (`UnramifiedTwistSwanStatement` in
`Langlands.Correspondence.Laumon.SlopeCalculus`). The universe of the representatives is that of
the carriers of `ρ`.

## Sources and the comparison

This is the class side of the bridge (b3) of the design note for Laumon's local Fourier
transform: `s(V)` is defined by Laumon (2.1.2.5) and is a natural number by Théorème (2.1.2.6),
p. 153 (`SlopeIntegralityStatement` in `Langlands.Correspondence.Laumon.SlopeIntegrality`).
Henniart (1988), §§4.1–4.2, pp. 509–510, attaches to an ℓ-adic representation its Artin and Swan
exponents and its slope, notes that an irreducible representation whose restriction to inertia is
irreducible has finite inertia image and `s(σ) = n(σ) λ(σ)`, and transports finite-image
representations between `ℚ̄_ℓ` and `ℂ` through an isomorphism of the algebraic closures of `ℚ`,
which preserves dimension and conductors. The Artin conductor of a finite-image representation of
inertia is the Swan conductor plus the codimension of the inertia invariants (Serre, *Local
Fields*, VI §2, Corollary 1', pp. 100–101), and the Swan conductor is the weighted sum of the
upper breaks (Serre IV §3).

The comparison uses only finite algebraic data and no continuity of `ι`. When `ℓ ≠ p`, an
irreducible ℓ-adic Galois representation has finite inertia image
(`Langlands.Henniart.LadicFiniteInertiaStatement`, proved by `Langlands.Henniart.ladicFiniteInertia`),
so its restriction to the Weil group and extension of scalars admit finite inertia presentations.
For every finite ramification subgroup, the dimension of the fixed space is the corank of a finite
linear system, which extension of scalars along `ι` preserves; these dimensions and the Herbrand
weights determine both `s(V)` and the complex Swan sum of the presentation
(`Langlands.Ramification.Local.FiniteUpperBreakWeightedSwan` and
`Langlands.Ramification.Local.FiniteUpperBreakArtinIdentity`, proved for all local fields by
`Langlands.Ramification.Local.finiteUpperBreakWeightedSwan` and
`Langlands.Ramification.Local.finiteUpperBreakArtinIdentity`). The Artin exponents of all
presentations agree (`Langlands.Ramification.Local.FiniteInertiaConductorIndependenceStatement`,
a clause of the statement proved by
`Langlands.Ramification.Local.inertiaSurjectivityPresentationAndConductorIndependence`). The
existence of the irreducible continuous Weil class in `LadicHasSwan` is
`Langlands.Henniart.LadicWeilTransportStatement`. This module states the comparison and does not
prove it.

## Declarations used

The module imports `Langlands.Correspondence.HenniartLadicStatement` and
`Langlands.Correspondence.Laumon.Slopes`. It uses `ladicSwan` of the latter and the Library's
`IrreducibleLadicClass`, `LadicHasSwan`, `ladicClassForget`, `ladicUnramifiedCharacters`,
`ladicUnramifiedTwist` and `FiniteRepresentation.classOf`. It uses no declaration of
weil-conjectures. Every declaration of this module depends at most on `propext`,
`Classical.choice` and `Quot.sound`.
