# Simple bases compatible with an integral coweight face

This internal construction uses a finite integral root datum
`P : RootDatum J M N` on its original perfectly paired additive groups.
The implementation takes `Fintype J`; no finite-generation or spanning
premise is imposed on `M` or `N`. Existence of a compatible base additionally
assumes that `P` is reduced.

## Regular refinement and the compatible base

`exists_regular_refinement` takes any integral coweight `ν : N` and produces
a coweight `f` regular on every root. For each root whose evaluation on `ν`
is nonzero, its evaluation on `f` has the same strict sign. This result
needs no reducedness premise.

The proof takes a regular integral root functional from
`RootDatumBase.exists_regular_functional`. Perfectness of the pairing
represents it by a coweight `f₀`. Set

```
n = 1 + ∑ i, |P.root' i f₀|,     f = n • ν + f₀.
```

At a root with nonzero integral evaluation on `ν`, the first term dominates
the second. At a root with zero evaluation on `ν`, regularity of `f₀`
proves regularity of `f`. These integer inequalities also prove the
claimed equality of nonzero signs, including for negative evaluations.

`exists_base_support` constructs a genuine integral `P.Base` whose support
is exactly `baseOf P.root (P.flip.toLinearMap f)` for any prescribed regular
`f`. For the root functional `q = P.flip.toLinearMap f`, its composition
with canonical copolarization gives a coroot functional `g`. The imported
integer canonical-form identities show that `g` is regular and its positive
coroot indices equal the positive root indices of `q`. The imported
`RootDatumBase.baseOf_root_eq_baseOf_coroot` identifies their indecomposable
positive indices. Integer linear independence and signed additive-monoid
generation give all four fields of `P.Base`. This adapts the imported base
construction while retaining its support, which a bare base-existence
theorem does not specify.

## The zero-root coroot span

For a base supported on the indecomposable positive roots of a sign
refinement, `coroot_span_zero_eq` proves

```
span ℤ (P.coroot '' {i | P.root' i ν = 0}) =
  span ℤ (P.coroot '' {i | i ∈ B.support ∧ P.root' i ν = 0}).
```

This comparison does not require reducedness once the compatible base is
supplied. Compose `P.flip.toLinearMap ν` with canonical copolarization.
The imported canonical norm identities identify its coroot zeros and
positive values with the root zeros and positive values of `ν`. Since
`ν` is nonnegative on each simple root of the refining base, this coroot
functional is nonnegative on all its simple coroots. The imported
`coroot_span_zero_eq_span_simple` then proves the displayed equality.

`Face` packages the regular refinement, compatible base and span identity;
`coweightFace` chooses one for every `ν` of a finite reduced datum.
`Face.annihilator_iff` identifies the annihilator of all zero-root coroots
with that of the selected simple coroots, by the span identity and kernel
containment. This last lemma requires neither finite index nor reducedness
once the package is supplied.

Given explicit finiteness of the zero-root reflection subgroup,
`Face.correction` applies `RootDatumBasedCorrection.correction` to any
automorphism fixing `ν`. It supplies the simple-index permutation,
preservation of the simple zero-root subset, and simultaneous pairing and
coroot formulas. `Face.correction_fixed` proves pointwise fixation of every
weight annihilating the selected simple coroots; this includes weights
outside the root span. These two adapters need no reducedness premise for
a supplied `Face`. They do not assert a group law as the automorphism varies.

The provenance is an internal deduction from the imported integral
root-pairing constructions and finite integer inequalities. No literature
statement is transcribed. The file constructs no actual algebraic group,
root datum, splitting field or Galois-fixed coweight. Identifying the
zero-root span with an actual Levi and the annihilator with an actual
cocenter character pullback remains a geometric comparison obligation.
