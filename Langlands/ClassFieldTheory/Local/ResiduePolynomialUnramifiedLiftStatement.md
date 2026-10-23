# Bounded unramified lifts of residue polynomial roots

`Langlands.LocalClassField.ResiduePolynomialUnramifiedLift.{u}` is a
`Prop`-valued definition. This module states the target and does not prove
it. Acceptance of this statement is not proof evidence for it.

## Exact statement

For every prime `p`, every `F : PadicField.{u} p`, and every polynomial
`P` over `F.canonicalTopologicalData.ResidueField` with
`0 < P.natDegree`, the statement asserts that there is an actual finite
intermediate field `K'` of `AlgebraicClosure F.Carrier / F.Carrier`
(a `FiniteIntermediateExtension F.Carrier`) such that:

- `K'.field` is Galois over `F.Carrier`;
- the canonical absolute ramification index of `K'.asPadicField (p := p)`
  equals that of `F`;
- `Module.finrank F.Carrier K'.field ≤ P.natDegree`;
- there is `z` in the canonical residue field of `K'.asPadicField (p := p)`
  with `(P.map φ).eval z = 0`, where `φ` is the actual
  `PadicField.TopologicalData.relativeResidueMap` from the canonical
  topological data of `F` to the canonical topological data of
  `K'.asPadicField (p := p)`.

The field `K'` lies in the specified algebraic closure
`AlgebraicClosure F.Carrier`. It is not an abstract extension. The universe
`u` is arbitrary. Finite dimensionality is part of
`FiniteIntermediateExtension`.

## Scalar maps

`K'.asPadicField (p := p)` is defined in
`Langlands.ClassFieldTheory.Local.ReciprocitySystem`. It repackages the same
field `K'.field` as a `PadicField p`. Its `Padic p`-algebra structure is
the composite `algebraMap F.Carrier K'.field ∘ algebraMap (Padic p)
F.Carrier`. The `F.Carrier`-algebra structure on its carrier is the
intermediate-field inclusion `algebraMap F.Carrier K'.field`.

The statement first installs the packaged algebra
`(K'.asPadicField (p := p)).algebra` with `letI`. It then installs the
scalar tower `Padic p → F.Carrier → K'.field` by
`IsScalarTower.of_algebraMap_eq' rfl`. This tower holds definitionally
because the packaged algebra is that composite. `relativeResidueMap`
elaborates against these exact instances. Installing only the tower,
without the packaged algebra, does not elaborate.

The residue map is defined in `Langlands.LocalField.RelativeIntegers`. It
is `IsLocalRing.ResidueField.map` of `relativeIntegerMap`, which restricts
`algebraMap F.Carrier K'.field` to the canonical valuation rings. On
residue classes it sends the class of an integer `x` of `F` to the class of
the inclusion image of `x` in `K'`. This holds by `rfl`
(`relativeResidueMap_residue`). By `relativeResidueMap_canonical`, for
canonical data this map equals `Langlands.Weil.Local.extensionResidueMap`.
No residue-field isomorphism or embedding is chosen independently.

## Unramifiedness encoding

The canonical absolute ramification index of a `PadicField` is
`ramificationIndex := (T.ord (p : F.Carrier)).toNat` for the canonical
topological data `T`, defined in
`Langlands.LocalField.Normalization.Definitions`. It is
the normalized valuation of `p`. Equality of these indices for `K'` and `F`
means that `K'/F` is unramified, because absolute ramification indices
multiply in towers. This is the same encoding that
`UnramifiedExtensionDegreeExistence` and
`PrimeNormAfterUnramifiedBaseChange` use.

## Scope

- Only `0 < P.natDegree` is assumed. `P` need not be monic, irreducible or
  separable, and it may have repeated factors.
- The degree bound is `≤ P.natDegree`, not equality. Degree one is allowed,
  for example when `P` already has a root in the residue field of `F`.
- The residue degree of `K'/F` is not stated separately. It equals
  `[K' : F]` because `K'/F` is unramified.
- No norm equation, critical-polynomial formula, compositum or
  compatibility of norm polynomials under residue extension is claimed.

## Original source and derived formulation

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`. The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. No
errata note for this source is recorded in the project.

- Chapter V, section 4, printed page 87 (PDF page 94), opens the setup: a
  finite extension of the residue field and the corresponding unramified
  extension `K'` of `K`.
- Chapter V, section 4, Proposition 6 and its proof, printed page 88 (PDF
  page 95). The proof uses a residue extension of degree at most `l`
  containing a root of the critical norm polynomial of degree `l`.
- Chapter III, section 5, Theorems 2–3, printed page 54 (PDF page 61), and
  Corollaries 1–3, printed page 55 (PDF page 62). These give the
  unramified extension with prescribed finite residue extension and its
  uniqueness and embedding properties. Theorem 2 also states that it is
  Galois exactly when the residue extension is.

This statement is a derived formulation, not a verbatim theorem of Serre.
Serre applies the step to one critical norm polynomial. Here it is stated
for every nonconstant residue polynomial. The informal argument is as
follows. An irreducible factor `Q` of `P` has degree `d ≤ P.natDegree`. Its
root generates a residue extension of degree `d`. This extension is
separable and Galois because residue fields are finite. Lifting it
unramifiedly as in III.5 gives a Galois `K'` of degree `d` whose residue
extension contains a root of `Q`, and hence of `P`. Realizing `K'` inside
`AlgebraicClosure F.Carrier`, expressing unramifiedness by canonical
absolute indices, and mapping `P` by the actual induced residue map are
encoding choices, not Serre's notation.

## Relation to existing results

`Langlands.ClassFieldTheory.Local.unramifiedExtensionDegreeExistence` in
`Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof` supplies
an unramified Galois intermediate field of every prescribed positive
degree. It does not identify a root of a given residue polynomial. A proof
of this statement can take such a field of degree `d`. It must then show
that its residue degree is `d`, through `e · f = [K' : F]`, and that a root
of `Q` exists in its residue field along the actual `relativeResidueMap`.
For the root, normality of finite field extensions applies. This module
supplies none of those steps. The target is intended as an ingredient of a
proof of `PrimeNormAfterUnramifiedBaseChange` in
`Langlands.ClassFieldTheory.Local.PrimeNormBaseChangeStatement`.

## Authors

The Lean statement was drafted by Worker 27. Worker 271 audited it against
the Library definitions and Serre's original, compiled it, refined the
docstring and wrote this Markdown.
