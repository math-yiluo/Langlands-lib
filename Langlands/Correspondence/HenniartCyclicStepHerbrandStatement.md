# The Herbrand function of a cyclic prime-degree step as a relative Herbrand function

The Lean module `Langlands.Correspondence.HenniartCyclicStepHerbrandStatement` contains
one proposition definition,
`Langlands.Henniart.CyclicPrimeStepHerbrandPsiStatement.{u}`. It is a statement and is
not proved here. The module imports
`Langlands.Correspondence.HenniartCyclicBaseChange` and
`Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof`. It defines nothing else.

## The statement

Let `p` be a prime, with `[Fact p.Prime]`, and let
`S : Langlands.Henniart.Numerical.CyclicPrimeStep.{u} p` be a cyclic step of prime
degree. Write `L = S.base` for its base and `M = S.top` for its top. `M` is an `L`-algebra
through `S.embedding`. Let `E : Langlands.LocalClassField.FiniteIntermediateExtension L.Carrier`
be a finite extension of `L` inside `AlgebraicClosure L.Carrier`, with underlying field
`E.field`. Assume that `M` and `E` are isomorphic as `L`-algebras, that is,
`Nonempty (S.top.Carrier ≃ₐ[S.base.Carrier] E.field)` for the algebra structure
`S.algebra`. Then the two real functions are equal:

```
S.herbrandPsi = Ramification.HerbrandBridge.relativeHerbrandPsi E
```

The statement is the equality of functions `ℝ → ℝ`, so it holds at every real number. It
quantifies over all `p`, `S` and `E`, with the fields in the universe `u`.

In words: `ψ_{M/L}`, computed in `M` with its canonical local-field structure, equals the
relative function `ψ_{E/L} = φ_{N/E} ∘ ψ_{N/L}`, computed in the Galois closure `N` of `E`.

## The parts of the statement

- `Numerical.CyclicPrimeStep`, `S.algebra` and `S.herbrandPsi` come from the module
  `Langlands/Correspondence/HenniartCyclicBaseChange.lean`. A step consists of p-adic fields
  `base` and `top`, an embedding `embedding : base.Carrier →ₐ[Padic p] top.Carrier`, a proof
  that `top` is Galois over `base`, and a proof that the Galois group has prime order.
  `S.algebra` is `Weil.Local.extensionAlgebra S.base S.top S.embedding`, the `L`-algebra
  structure on `M` that the embedding gives. `S.herbrandPsi` is
  `Ramification.Padic.herbrandPsi S.top.canonicalTopologicalData S.base.Carrier`. This is the
  Library's inverse Herbrand function of the finite Galois extension `M/L`, built from the
  lower ramification groups of `M/L` for the canonical local-field structure
  `S.top.canonicalTopologicalData` of `M`.
- `Langlands.LocalClassField.FiniteIntermediateExtension K` is the Library's type of
  finite-dimensional intermediate fields of `AlgebraicClosure K` over `K`
  (`Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean`). The base `L` is found from the
  type of `E`.
- `Langlands.Ramification.HerbrandBridge.relativeHerbrandPsi E` comes from
  `Langlands/LocalFactor/Ramification/Herbrand/SubextensionProof.lean`. It is defined even when
  `E/L` is not Galois. Let `N = galoisClosure E` be the normal closure of `E.field` over `L`
  inside `AlgebraicClosure L.Carrier` (Mathlib's `IntermediateField.normalClosure`), a finite
  Galois extension of `L` that contains `E`. Then `relativeHerbrandPsi E` is
  `relativeIndex L N _`, that is, `φ_{N/E} ∘ ψ_{N/L}`. Here `ψ_{N/L}` and `φ_{N/E}` are the
  Library's `Ramification.Padic.herbrandPsi` and `Ramification.Padic.herbrandPhi` of `N`,
  viewed as a Galois extension of `L` and of `E` respectively, for its canonical local-field
  structure.
- The isomorphism hypothesis uses `Nonempty` because the conclusion does not depend on the
  choice of isomorphism. The `letI := S.algebra` inside the hypothesis makes
  `≃ₐ[S.base.Carrier]` refer to the `L`-algebra structure of the step. On `E.field` the
  `L`-algebra structure is the one of an intermediate field.

## Provenance

This is an internal comparison of two Library definitions of the same function. It is not a
numbered result of a source. The mathematics is in Serre, *Local Fields* (registered source
`serre-1979-local-fields`), Chapter IV §3, pp. 73-75:

- On pp. 73-74, `φ` and its inverse `ψ` of a finite Galois extension are defined from the
  lower ramification groups of that extension. These groups depend only on the extension and
  its valuation, so an isomorphism of extensions over the base carries the groups of one
  extension to those of the other. Hence `ψ` is the same for `L`-isomorphic Galois extensions.
  In the Library this invariance is
  `Langlands.Ramification.HerbrandBridge.herbrandPsi_eq_of_algEquiv`
  (`Herbrand/TransportProof.lean`).
- Remark 2 on p. 75 defines `φ_{E/K} = φ_{L/K} ∘ ψ_{L/E}` for a subextension `E` of a Galois
  extension `L/K`, independently of `L`. Its inverse is `ψ_{E/K} = φ_{L/E} ∘ ψ_{L/K}`, the
  function that `relativeHerbrandPsi` implements with `L` the Galois closure.
- When `E/L` is Galois, as it is here because `E` is `L`-isomorphic to the Galois extension
  `M`, the Galois closure of `E` is `E` itself. Then `φ_{E/E}` is the identity and the relative
  function is `ψ_{E/L}`, which equals `ψ_{M/L}` by the first point.

The two Library definitions realize the fields differently: `S.herbrandPsi` works in the
abstract field `S.top.Carrier`, and `relativeHerbrandPsi E` works in a subfield of
`AlgebraicClosure L.Carrier`. The statement records that they agree.

## Why the statement is needed

Lemma `lem:tower` of the operator's route note
(`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`, lines 1196-1213)
builds a tower of cyclic extensions of prime degree and computes the Herbrand function of each
step. `Langlands.Henniart.CyclicTowerStatement` (module `HenniartCyclicTower`) states that lemma along
`CyclicPrimeStep`s and their `herbrandPsi`, and `cyclicTower` (module
`HenniartCyclicTowerProof`) proves it. The Kummer steps of that proof are fields `L(ϖ^{1/p})`
with `ϖ` a uniformizer of `L`.

The published Kummer-step formula
`Langlands.Ramification.Kummer.KummerStepHerbrandPsiStatement`, proved as
`Langlands.Ramification.Kummer.kummerStepHerbrandPsi`, is stated for
`relativeHerbrandPsi (adjoinFiniteIntermediate L α)` of an intermediate field `L(α)` with
`α ^ p` a uniformizer. With the present statement that formula applies to a
`CyclicPrimeStep` whose top is `L`-isomorphic to `L(α)`.
