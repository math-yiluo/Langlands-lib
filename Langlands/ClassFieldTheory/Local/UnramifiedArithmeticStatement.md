# Finite unramified extensions and arithmetic Frobenius coordinates

Author: Worker 154.

This pair states two arithmetic prerequisites for constructing the absolute
local invariant from finite unramified stages. Both declarations are
proposition-valued definitions; this pair proves neither assertion.

`UnramifiedExtensionDegreeExistence.{u}` says that for every prime `p`,
every `F : PadicField.{u} p`, and every positive natural number `n`, the
specified `AlgebraicClosure F.Carrier` contains a finite Galois intermediate
field of degree exactly `n` whose canonical absolute ramification index
equals that of `F`.

The conclusion uses the existing `FiniteIntermediateExtension`, which
packages an actual intermediate field and its finite-dimensionality
certificate. Its `asPadicField` wrapper uses the composite p-adic scalar
map through `F.Carrier` and leaves the underlying field unchanged.
The degree is the dimension of this same field over `F.Carrier`.
The field and its algebraic closure have the arbitrary base universe `u`.
The assertion includes degree one and makes no uniqueness claim.

`ArithmeticUnramifiedCoordinateExistence.{u,v}` concerns every compatible
finite Galois extension `E/F` of p-adic fields in independent universes.
Compatibility means that the specified p-adic algebra structures and the
specified `F`-algebra structure on `E` form an `IsScalarTower`. Assuming
equality of their canonical absolute ramification indices, it asserts
the existence of an equivalence

`Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod d)`,

where `d = Module.finrank F.Carrier E.Carrier`. The local `NeZero d`
instance is proved from finite-dimensional field degree positivity;
it is not an additional premise.

The conclusion uses the published `IsArithmeticUnramifiedCoordinate`
predicate from [Invariants](Invariants.md). It requires injectivity of
the actual residue action `LocalGalois.residueHom` and requires the inverse
image of the positive coordinate `1` to act on the actual extension
residue field by `x ↦ x^q`, where `q` is the cardinality of the actual base
residue field. Thus the convention is arithmetic Frobenius. The predicate
uses the canonical norm on the base and the resulting spectral
extension valuation; no abstract replacement residue field or supplied
Frobenius action appears in the assertion. Degree one is included.

In both targets, equality of canonical absolute ramification indices
expresses unramifiedness for compatible finite p-adic extensions.
The indices are the normalized additive orders of the same rational
prime. In this setting their equality is equivalent to relative
ramification index one, and the residue fields are finite and hence
perfect. A proof must establish the required links to the actual
spectral residue constructions; the statement assumes no such comparison
theorem as an extra hypothesis.

These assertions provide neither an invariant nor its compatibility with
inflation or restriction. They do not assert that a cohomology class
splits over an unramified extension; that is the separate
`UnramifiedH2Exhaustion` target. Conversely, class-dependent exhaustion
does not supply every positive degree or an arithmetic coordinate.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, Greenberg English translation, Springer
GTM 67 (1979), registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 154 read Chapter III, section 5, Theorems 2 and 3 and their
corollaries, printed pages 54–55 / PDF pages 61–62, and Chapter XIII,
section 2, example (a), printed page 191 / PDF page 196. No project errata
entry for this source was present when checked.

Theorems 2 and 3 identify unramified extensions of a complete discretely
valued field with separable residue extensions and identify the associated
Galois groups. Applied to finite residue fields, this gives a finite
unramified Galois extension of each positive degree. An embedding into
the specified algebraic closure realizes the first target's actual
intermediate field. Example (a) supplies the finite-field arithmetic
Frobenius convention and cyclic Galois group: the positive generator acts
by the base-residue-cardinality power. Combined with the unramified
residue comparison, this gives the second target.

The Lean formulation is a derived specialization of these source results
to the project's canonical p-adic models, its actual algebraic closure
and residue action, and the existing cyclic-coordinate predicate.
Independent universes express the freedom to use any finite extension
carrier; they add no mathematical hypothesis. Proving these statements
requires the finite-field, lifting, degree, valuation and residue-map
comparisons rather than assuming a class formation or local reciprocity.
