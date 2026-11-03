# Homogeneous bases of the augmentation cotangent space

Module `Langlands.GroupScheme.Rational.TorusUnipotence.CotangentBasis`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

Let `k` be a field, `A` a commutative `k`-algebra and `ε : A →ₐ[k] k` an augmentation with
augmentation ideal `I = ker ε`. The module defines the cotangent class map `A → I / I²`. For a
graded `A`, it shows that `I / I²` has a basis of classes of homogeneous elements of nonzero
degree once the degree-zero part of `I` lies in `I²`. `BigCell` uses this basis to choose the
variables of its truncated polynomial rings.

## Definition

`cotangentMap ε : A →ₗ[k] (RingHom.ker ε).Cotangent` sends `a` to the class of `a - ε(a) · 1` in
`I / I²` (`Ideal.toCotangent`).

## Statements

* `cotangentMap_of_mem`: for `a ∈ I`, `cotangentMap ε a` is the class of `a`.
* `cotangentMap_eq_iff`, `cotangentMap_eq_zero_iff`: for `a, b ∈ I`, the classes agree iff
  `a - b ∈ I²`, and the class of `a` is `0` iff `a ∈ I²`.
* `cotangentMap_algebraMap`: constants have class `0`.
* `cotangentMap_mul a b` (Leibniz rule):
  `cotangentMap ε (a * b) = ε a • cotangentMap ε b + ε b • cotangentMap ε a`.

Now let `𝒜 : ι → Submodule k A` be a grading (`GradedAlgebra 𝒜`) by an additive monoid `ι` with
decidable equality, and assume `ε` vanishes on `𝒜 i` for `i ≠ 0` (`hε`).

* `augmentation_decompose_zero`: `ε` of the degree-zero component of `a` equals `ε a`.
* `span_homogeneous_cotangent hε hI0`. Assume also that every `a ∈ 𝒜 0` with `ε a = 0` lies in
  `I²` (`hI0`). Then the classes `cotangentMap ε a` of homogeneous `a ∈ 𝒜 i` with `i ≠ 0` span
  `I / I²`.
* `exists_homogeneous_cotangent_basis hε hI0`. Under the same hypotheses there is a basis
  `b : Basis σ k (I / I²)` with elements `z s ∈ 𝒜 (w s)`, `w s ≠ 0`, and
  `cotangentMap ε (z s) = b s` for every `s`.

## Proof

The linearity of `cotangentMap` and the Leibniz rule are computations in `A`. For the Leibniz
rule, write
`a b = (a - ε a)(b - ε b) + ε a · b + ε b · a - ε a ε b`; the first product lies in `I²`, and
constants have class `0`.

For `augmentation_decompose_zero` and `span_homogeneous_cotangent`, induct over the
decomposition of `a` into homogeneous components (`DirectSum.Decomposition.inductionOn`). This
shows that `cotangentMap ε a - cotangentMap ε (a₀)` lies in the span of the classes of homogeneous
elements of nonzero degree, where `a₀` is the degree-zero component of `a`. If `a ∈ I`, then
`a₀ ∈ I` by `augmentation_decompose_zero`, so `a₀ ∈ I²` by `hI0` and its class is `0`. Every element of
`I / I²` is a class of some `a ∈ I` (`Ideal.toCotangent_surjective`).

For the basis, `exists_linearIndependent` extracts a linearly independent subset `B` of the
spanning set with the same span. `Module.Basis.mk` turns it into a basis, and `choose` picks a
homogeneous representative `z s` of nonzero degree `w s` for each basis vector.

## Provenance

These are standard facts about cotangent spaces of augmented graded algebras, proved here as
internal lemmas for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. No source states them in
this form.
