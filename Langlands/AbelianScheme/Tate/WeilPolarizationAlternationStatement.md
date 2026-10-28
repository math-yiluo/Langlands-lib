# Conditional alternation of the integral polarization Weil pairings

`IntegralPolarizationWeilAlternationStatement` asserts alternation of the
existing integral Weil pairing pulled back in the second variable by an
actual relative polarization. It is a proposition definition; this file
does not prove it.

The input homomorphism `lam` goes from the actual abelian scheme `A/S` to
its constructed `dualAbelianSchemeFromEvaluation`. Its hypothesis is the
published `IsPolarization` predicate: an actual isogeny with an ample
Mumford presentation on every geometric fibre after a possible field
extension. In particular, neither a supplied bilinear form nor a
diagonal identity replaces that predicate.

Two relative theorem dependencies are explicit:

- `RelativeFiniteWeilTransitionStatement` is used in the construction of
  the inverse-limit pairings.
- `RelativeFiniteWeilAlternationStatement` asserts the diagonal identity
  of the actual finite scheme pairing of this polarization.

The other inputs are the seven tensor/Picard propositions used by the
pairing constructors, the square and universal-base-change propositions
used by `IsPolarization`, the actual dual witness and its geometry, and
an inverse Poincare line bundle with its evaluation isomorphism. The
base `S` is quasi-separated. The conclusion holds for every test scheme
`T/S`, including nonreduced test schemes.

The three conclusions use Mathlib's `LinearMap.IsAlt`, meaning
`b x x = 0` for every input `x`:

- For every predicate `P` on torsion orders, the selected integral
  pairing `integralWeilAlongHomBilinearMap ... lam P` is alternating
  over the existing full profinite-integer scalar ring. The full Tate
  pairing is its specialization to `P := fun _ => True`.
- For every natural modulus `m`, the away pairing
  `awayWeilAlongHomBilinearMap ... lam m` is alternating over the
  existing prime-to-`m` profinite-integer scalar ring.
- For every prime `p`, expressed by `Fact p.Prime`, the actual
  prime-adic pairing `primeWeilAlongHomBilinearMap ... p lam` is
  alternating over the p-adic integers.

All values remain in their constructed roots-of-unity inverse limits:
the selected/full, away, or prime-adic integral Tate twist. Additive
zero in these twists means the identity root of unity at every level.
No compatible primitive roots or twist trivialization is chosen.

This is an internal consequence target for the existing finite
scheme-diagonal statement and the existing coordinate comparisons.
The finite statement applies at the positive orders in every selected
system and at every `p^n`. Testing its scheme-morphism equality on a
torsion point gives a trivial diagonal value, and coordinatewise
equality in the inverse limit then gives the displayed conclusions.
A separate proof must implement that argument.

The deep relative finite alternation theorem remains an explicit
unproved dependency; the field corollary motivating that theorem
does not establish it over an arbitrary base. This statement adds no
axiom and claims no unconditional alternation, nondegeneracy,
perfectness, rational or adelic alternation, or monodromy equivariance.
