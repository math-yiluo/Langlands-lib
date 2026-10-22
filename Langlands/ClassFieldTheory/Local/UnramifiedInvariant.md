# Finite unramified H2 invariants through the actual norm quotient

Author: Worker 159.

The module defines `unramifiedH2InvariantEquiv` and `unramifiedH2Invariant`
in the namespace `Langlands.ClassFieldTheory.Local`. For every prime `p`, let
`F : PadicField.{u} p` and `E : PadicField.{v} p` have a compatible algebra
structure, scalar tower over `Padic p`, finite dimension, and Galois structure.
The carrier universes `u` and `v` are independent. Write
`d = Module.finrank F.Carrier E.Carrier`. The unramified hypothesis is exactly

```lean
F.canonicalTopologicalData.ramificationIndex =
  E.canonicalTopologicalData.ramificationIndex
```

The other explicit input is an equivalence

```lean
χ : Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod d)
```

For these inputs the definitions give an additive equivalence and its
composition with the subgroup inclusion:

```text
relativeCohomology F.Carrier E.Carrier 2 ≃+ denominatorSubgroup d
relativeCohomology F.Carrier E.Carrier 2 →+ RationalModIntegers
```

The source is the published ordinary cohomology of the actual Galois action
on extension-field units. `RationalModIntegers` is the actual additive quotient
of the rationals by the subgroup of integers. `denominatorSubgroup d` is the
subgroup annihilated by `d`. Positivity of `d` is supplied internally by
`Module.finrank_pos`; the construction imposes no hypothesis `1 < d`.

## Elementary denominator algebra

For a positive natural number `d`, `denominatorMap d hd` is the additive map
from `ZMod d` to `RationalModIntegers` induced by

```text
z : ℤ ↦ rationalClass ((z : ℚ) / d).
```

The private `rationalClass_eq_zero` identifies vanishing of a rational class
with existence of an integer equal to that rational number. The private
`integerFraction` is the displayed integer homomorphism; its value at `d`
vanishes since `d/d = 1`. `ZMod.lift` therefore descends it to `denominatorMap`.
`denominatorMap_intCast` proves the formula for every integer representative,
including negative integers.

For injectivity, if `z/d` is an integer `k`, multiplication by the nonzero
rational number `d` gives `z = d*k`, so `z` is zero in `ZMod d`. Its image is
annihilated by `d` because the same is true in `ZMod d`. Conversely, lift any
element of `denominatorSubgroup d` to a rational representative `q`.
Its annihilation says that `d*q` is an integer `k`; the class of `k` modulo
`d` maps to the original element. These facts define

```lean
denominatorEquiv (d : ℕ) (hd : 0 < d) : ZMod d ≃+ denominatorSubgroup d
```

`denominatorEquiv_intCast` states the integer representative formula after
subgroup inclusion. `denominatorEquiv_apply` states the equivalent formula
using `ZMod.cast x : ℚ`, the canonical representative interpreted in the
rationals. The proof first lifts that representative to `ℤ` and uses
`ZMod.intCast_zmod_cast` and `ZMod.intCast_cast`.
`denominatorEquiv_one` proves that the image of `1` after inclusion is
`reciprocalClass d`. Its proof uses the integer representative `1`, so it also
covers `d = 1`, when both classes are zero.

## Cyclic generator and norm quotient

`cyclicCoordinateGenerator χ` is exactly
`χ.symm (Multiplicative.ofAdd 1)`. The general certificate
`cyclicCoordinateGenerator_generates` applies to any group with an equivalence
to `Multiplicative (ZMod d)`. For any group element, lift its coordinate to an
integer `k`; compatibility of the equivalence with integer powers proves
that the element is the `k`th power of this generator. This proof includes the
trivial group and does not require positivity of `d`.

`unramifiedNormOrderEquiv` is an additive equivalence from
`Additive (NormQuotient F.Carrier E.Carrier)` to `ZMod d`. Its private existence
proof specializes the published theorem
`Langlands.LocalClassField.unramifiedCyclicNormQuotient` to the canonical
topological data. It then forgets the continuity certificates and changes
multiplicative notation to additive notation with `toAdditiveLeft`. The
source topology and the published theorem are unchanged. Classical choice
selects this specified additive equivalence.

`unramifiedNormOrderEquiv_projection` retains the theorem's formula:

```text
unramifiedNormOrderEquiv F E hram
  (Additive.ofMul (normQuotientProjection F.Carrier E.Carrier a))
  = (F.canonicalTopologicalData.ord (a : F.Carrier) : ZMod d).
```

Thus this is the actual determinant norm quotient, and no norm-quotient
existence premise remains in the construction. This intermediate equivalence
requires no Galois assumption; the H2 construction adds the Galois assumption.

## The invariant and its certificates

`unramifiedH2InvariantEquiv` composes, in order:

1. `cyclicH2NormEquiv` for `cyclicCoordinateGenerator χ` and its proved
   generation certificate;
2. `unramifiedNormOrderEquiv` for the canonical unramified index equality;
3. `denominatorEquiv d Module.finrank_pos`.

`unramifiedH2Invariant` follows this additive equivalence with the inclusion
of `denominatorSubgroup d` in `RationalModIntegers`.

`unramifiedH2Invariant_normRepresentative` evaluates this homomorphism on

```text
(cyclicH2NormEquiv F.Carrier E.Carrier
  (cyclicCoordinateGenerator χ)
  (cyclicCoordinateGenerator_generates χ)).symm
  (Additive.ofMul (normQuotientProjection F.Carrier E.Carrier a))
```

and proves the result is
`rationalClass ((F.canonicalTopologicalData.ord (a : F.Carrier) : ℚ) / d)`.
The proof cancels the cyclic equivalence with its inverse and applies the
published norm representative formula and the integer denominator formula.

`unramifiedH2Invariant_injective` composes injectivity of the equivalence
with injectivity of the subgroup inclusion.
`unramifiedH2Invariant_range` proves that the homomorphism's range is exactly
`denominatorSubgroup d`: one inclusion is subtype membership, and the other
uses the inverse equivalence on a subgroup element.
`unramifiedH2Invariant_degree_one` explicitly proves that the invariant of
every class is zero when `d = 1`, by its annihilation by `1`.

The coordinate `χ` is explicit throughout. This module does not identify it
with an arithmetic residue coordinate. In particular, the value theorem is
about the inverse cyclic norm equivalence, not about the separately defined
carry cocycle. There is no `CyclicClassNormNormalization`, absolute invariant,
or class-formation premise. Arithmetic Frobenius existence, carry-class
normalization, tower compatibility, base change, and absolute descent are
outside the claims of this module.

## Provenance

This is a derived construction from the published modules
[`CyclicNorm`](CyclicNorm.md),
[`UnramifiedCyclicNormQuotientProof`](UnramifiedCyclicNormQuotientProof.md),
and the rational quotient definitions in [`Cohomology`](Cohomology.md).
It adds elementary quotient-group algebra and the explicit composition;
all imported Lean/Markdown pairs are preserved. Imported results are used
by Lean name, and their authors' proofs are not copied.

The mathematical background is Jean-Pierre Serre, *Local Fields*, English
translation by Marvin Jay Greenberg, GTM 67, Springer, 1979:

- Chapter V, Section 2, Proposition 3(c), printed p.82/PDF p.89, with the
  following finite-residue-field remark, supplies the unramified valuation
  quotient underlying the imported norm theorem.
- Chapter XIII, Section 3, Proposition 6 and the following explicit
  description, printed p.193/PDF p.198, describe the local invariant via
  valuation and evaluation at Frobenius. They motivate the positive fraction
  convention here. This module only constructs the stated finite-stage map
  for an explicit cyclic coordinate; it does not formalize the absolute
  isomorphism or establish the Frobenius identification from that page.

Worker 159 read both cited original pages. Registered source:
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No source-specific errata file was present in the project notes.
