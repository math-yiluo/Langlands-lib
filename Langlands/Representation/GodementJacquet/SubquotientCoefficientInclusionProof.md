# Bi-smooth coefficients of actual subquotients

Worker 55 proves the two existing closed propositions from
`Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionStatement`.
The closing theorems are
`Langlands.GodementJacquet.subquotientCoefficientInclusion` and
`Langlands.GodementJacquet.Padic.subquotientCoefficientInclusion`.

## General proof

Let `σ` be a smooth complex representation of a topological group whose compact
open subgroups are cofinal among open subgroups. Let `A` be an actual
subrepresentation of `σ`, and let `q : A.toRepresentation.IntertwiningMap τ`
be surjective. The inclusion `i : A.toRepresentation.IntertwiningMap σ` has
the actual submodule inclusion as its underlying linear map. It is injective,
so `isSmooth_of_injective i` gives smoothness of the inherited representation
of `A`.

By `Submodule.span_le`, it suffices to treat a generator
`biSmoothCoefficient τ ℓ v`, where `ℓ` is an actual smooth functional on `τ`
and `v` is an actual smooth vector. Pull back `ℓ` through `q` using
`contragredientMap q`. The published
`contragredientMap_surjective_of_injective_of_compact_cofinal`, applied to
`i`, extends this smooth functional to a smooth functional `m` on `σ`.
Both representations needed by that extension theorem are smooth: the
inherited representation of `A`, as just proved, and the assumed ambient
representation `σ`. No smoothness premise on `τ` is needed.

Choose `w ∈ A` with `q w = v` using the given surjectivity. Its actual ambient
vector `(w : V)` is smooth by smoothness of `σ`. The extension identity,
evaluated at `A.toRepresentation g w`, gives

```text
m (σ g (w : V)) = ℓ (q (A.toRepresentation g w)).
```

The intertwining equation and `q w = v` identify the right side with
`ℓ (τ g v)`. Function extensionality therefore identifies
`biSmoothCoefficient σ m ⟨(w : V), hσ (w : V)⟩`
with the original coefficient of `τ`. This is a generator of the actual
ambient coefficient span, and `Submodule.subset_span` gives its membership.
Passing to spans proves exactly
`biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ`.

The group universe and both complex module carrier universes are independent.
The proof uses the specified subrepresentation and surjective intertwiner
directly. It adds no irreducibility, admissibility, finite-length, model
equivalence, or analytic premise.

## Canonical p-adic specialization

For each prime `p`, field `F : PadicField p`, and natural number `n`, install
exactly `F.canonicalTopologicalData.topology` and its proved general-linear
topological-group instance at actual rank `n + 1`. Given an open subgroup `K`,
its underlying set is a neighborhood of the identity. The published
`F.canonicalTopologicalData.generalLinearCompactOpen (n + 1)` returns a compact
open subgroup `L` contained in `K`. Its compactness and containment are exactly
the cofinality witnesses needed by the general theorem.

Apply the general theorem with those witnesses and the original data
`σ`, `τ`, `A`, and `q`. This discharges cofinality internally; the p-adic
theorem adds no premise. The argument works for every `n`, including `n = 0`,
which gives actual rank one. The field universe and both module universes
remain independent.

## Provenance and scope

This is an internal derived proof using the Library's actual coefficient
definitions, smooth contragredient exactness, smoothness transfer, and canonical
general-linear compact-open constructions. The statement pair records the
motivating constituent coefficient restriction from JPSS, Section 5.4,
printed page 423; the present general assertion is not claimed as a literal
numbered theorem from that source. The implemented route is the algebraic
smooth-functional extension argument described above.

All imported Lean and Markdown pairs, including the statement pair, are used
unchanged. The proof has no dependency on Godement–Jacquet analytic base proofs,
two-block or finite-block multiplicativity, or Section 7 descent. The
coefficient inclusion alone supplies neither analytic existence nor identities
of normalized generators or factors. Those are separate analytic obligations.

Worker 55 authored this proof and explanation. The earlier published statement
pair was authored by Worker 468 and Worker 55; it is imported unchanged.
