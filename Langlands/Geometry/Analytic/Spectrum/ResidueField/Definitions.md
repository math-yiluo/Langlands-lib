# Construction of completed residue fields

Author: Worker 36.

For a bounded multiplicative spectrum point x of a normed commutative
algebra A over an ultrametric normed field K, these definitions construct
its completed residue field and a bounded K-algebra map from A into it.
The field and algebra have independent universes. Neither is assumed
complete, and the norm on A need not satisfy the strong triangle inequality.

The separate `Spectrum.Nonarchimedean` theorem proves that x itself does
satisfy the strong triangle inequality. `toValuation` packages its
nonnegative values as a valuation into the nonnegative reals. The actual
quotient `ResidueDomain x` is A/ker(x), an integral domain by the published
prime-kernel theorem. `residueQuotient` is the algebraic quotient map.
Mathlib's quotient valuation defines `residueValuation`. Its value is zero
exactly on zero, proved by taking representatives and applying the
quotient's zero criterion. Thus all nonzero denominators avoid its support.

`ResidueFraction x` is the actual fraction field of that quotient.
Mathlib's valuation extension to localization gives `fractionValuation`,
whose restriction along the composite `fractionMap` recovers x.
Coercing the values to the reals gives `fractionAbsoluteValue`.
`NormedResidueField K x` is the `WithAbs` type for that absolute value,
so its norm explicitly depends on x. `residueFieldMap` composes the
quotient and fraction-field maps with this type equivalence.

Scalar normalization proves that the resulting K-algebra structure
preserves the norm of each scalar, which gives a normed algebra structure.
The valuation's strong triangle inequality gives an ultrametric distance.
`CompletedResidueField K x` is its actual uniform-space completion.
Mathlib supplies its complete normed field and normed K-algebra structures;
the strong triangle inequality extends by density and closedness.
`completedResidueMap` is the composite map from A, with norm bound one.
`residueCompletionMap` is the canonical ring homomorphism from the normed
fraction field to its completion. No field, extension valuation, completion,
or realizing evaluation map is assumed as input.

This follows the completed residue-field construction immediately after
Exercise 1.2.4 of Berkovich's *Non-archimedean analytic spaces* (Trieste
2009), p.4, with spectrum conventions from Definition 1.2.3. The incomplete
source generality is derived: these quotient, fraction, and completion
constructions do not require completeness of A or K. The construction uses
the absolute value induced by x, rather than identifying it with a quotient
of the ambient norm on A. It does not assert spectrum nonemptiness or
construct an analytic domain or structure sheaf.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
