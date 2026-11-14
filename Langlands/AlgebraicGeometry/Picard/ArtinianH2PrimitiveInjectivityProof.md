# Proof: reduced-coproduct injectivity on the ideal H² of elementary Artinian thickenings

Module `Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityProof`.
Author: Worker 858.

The theorem `Langlands.AbelianScheme.artinianH2PrimitiveInjectivity` proves the
published proposition
`Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.{u}` exactly, with
no hypotheses.

The statement is about a surjection `φ : B' →+* B` of local Artinian rings in
`Type u` with `maximalIdeal B' * RingHom.ker φ = ⊥`, and an abelian scheme `A` over
`Spec B'`. Let `I` be the actual ideal sheaf of the special fibre of `A`, and `IP`
the ideal sheaf of the special fibre of `P = A ×_(Spec B') A`. For every
compatible coefficient map `k` along `m`, `p1` and `p2`, the theorem gives

```text
pull m km − pull p1 k1 − pull p2 k2 : H²(A, I) → H²(P, IP)
```

is injective. Here `pull f k` is the canonical cohomology pullback followed by the
adjoint of `k`, exactly as in
[`ArtinianH2PrimitiveInjectivityStatement`](ArtinianH2PrimitiveInjectivityStatement.md).

## Implemented proof

The proof is one term with three published inputs from the Library.

1. `Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.of_naturality`,
   from [`ArtinianH2PrimitiveInjectivityReduction`](ArtinianH2PrimitiveInjectivityReduction.md).
   It proves
   `ArtinianH2PrimitiveInjectivityReductionStatement.{u}`, which is
   `NaturalityStatement.{u} → FieldH2PrimitiveInjectivityStatement.{u} →
   ArtinianH2PrimitiveInjectivityStatement.{u}`.
   It writes ideal cohomology in finitely many residue-fibre coordinates. In each
   coordinate it identifies the three maps with structure-sheaf pullbacks on the
   residue fibre `A_k` over `k = ResidueField B`, and then applies the field case
   to `A_k`.
2. `Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.naturalityStatement`,
   from
   [`ElementaryArtinianIdealCohomologyNaturalityProof`](ElementaryArtinianIdealCohomologyNaturalityProof.md).
   It proves the first hypothesis, `NaturalityStatement.{u}`.
3. The second hypothesis, `FieldH2PrimitiveInjectivityStatement.{u}`, is the term
   `fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison
   fieldH2ExteriorCoproductComparison`.
   - `Langlands.AbelianScheme.fieldH2ExteriorCoproductComparison`, from
     [`FieldH2ExteriorCoproductComparisonProof`](../../AbelianScheme/FieldH2ExteriorCoproductComparisonProof.md),
     proves `FieldH2ExteriorCoproductComparisonStatement.{u}`. That statement gives
     `H²(A, O_A) ≅ ⋀² H¹(A, O_A)` together with a Künneth-type decomposition of
     `H²(A × A, O)`, and explicit formulas for `p1*`, `p2*` and `m*` on it.
   - `Langlands.AbelianScheme.fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison`,
     from
     [`FieldH2ExteriorCoproductComparisonStatement`](FieldH2ExteriorCoproductComparisonStatement.md),
     turns that comparison into injectivity. It projects onto the middle tensor
     component and uses injectivity of `⋀² → ⨂²`.

All three inputs live in the same universe `u` as the target. The proof adds no
lemmas, definitions or options. `lean_check` reports zero errors and zero
warnings. The axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Constraint check

The task forbids routing through the Artinian line-bundle lifting, Picard-zero
lifting, dual-scheme geometry and smooth-family representability statements. None
of those names occurs in any Langlands module in the import closure of this file.
I checked this by scanning the closure, about 2,065 modules, at Library commit
`ba00e097`.

## Provenance

This proof is an internal assembly. The mathematical route follows
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Chapter 6, proof
of Proposition 6.7, p.118. The provenance is recorded in the statement's Markdown
and in the reduction's Markdown. This file only composes published Library
results.
