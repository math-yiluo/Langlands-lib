# Hilbert equivalences induced by actual full-operator equivalences

This internal construction transports an actual whole-operator equivalence to
an isometric equivalence of actual Hilbert completions. The number field has
arbitrary universe `uF`, the matrix rank is any natural number, and the
coefficients are complex. The inputs are actual `OperatorRealization F n`
spaces `S`, `T`, a supplied form `c : T.UnitaryForm`, and an actual
`e : S.Equivalence T`.

The original spaces are represented subspaces of stable automorphic functions.
The equivalence respects all finite, compact and enveloping-algebra operators.
The published `c.ofEquivalence e` pulls back the single positive form, retaining
its finite and compact invariance and its skewness for genuine real Lie
directions. It has the identity

```text
(c.ofEquivalence e).inner f g = c.inner (e f) (e g).
```

`completedEquivalence c e` is a complex-linear isometric equivalence from
`(c.ofEquivalence e).finiteForm.HilbertCompletion` to
`c.finiteForm.HilbertCompletion`. It applies the generic
`InvariantPositiveForm.completedEquiv` to the finite restriction of the same
original equivalence and its actual surjectivity. The forward map is the
published completed isometry of that restriction. The generic
`completedEquiv_toHilbert` therefore gives, without another chosen map,

```text
completedEquivalence c e (j_source f) = j_target (e f).
```

The complete extension laws remain in the generic invariant-positive-form
namespace. For arbitrary supplied forms `b : S.UnitaryForm`, `c : T.UnitaryForm`,
a whole-operator intertwiner `L`, and the form-preservation identity, apply
`completedIsometry` to `b.finiteForm`, `c.finiteForm` and
`Intertwiner.finiteRestriction L`. Its published laws give an injective
isometric complex-linear extension, the embedded-vector formula, finite
covariance, a closed finite-invariant range and the identification of that range
with the closure of the original embedded image.

The accompanying `CompletionTransport` adds uniqueness of a continuous linear
extension, surjectivity from original surjectivity, covariance under additional
continuous operators with their prescribed embedded-vector formulas, and
stability of the same completed range under those operators. It also constructs
the generic isometric equivalence used by the actual constructor here. The
generic group, source and target carrier universes are independent.

For the actual compact actions, the additional algebraic operators are
`S.compactRepresentation k` and `T.compactRepresentation k`. Their continuous
extensions are the already constructed isometries
`b.compactForm.completedOperator k` and `c.compactForm.completedOperator k`.
Their `toLinearIsometry.toContinuousLinearMap` maps supply the continuous maps
required by the adapter. Each compact form retains exactly its finite form's
positive core, so its completion, structures and embedding agree definitionally
with those of the finite form. The published `completedOperator_toHilbert`
formulas and `Intertwiner.compact L k` supply the adapter hypotheses. Thus its
covariance and range-stability laws apply on the same actual completions.
No continuity of the whole compact action is required for this operator-by-operator
conclusion. The same reasoning applies to the constructor's pulled-back form
and `e.toIntertwiningMap`.

The construction and proofs derive from published `OperatorUnitaryForm`,
`OperatorEquivalence`, and `Representation/Unitary/CompletionIntertwiner`.
The additional density, covariance and surjectivity arguments are internal
consequences; there is no new original-literature identification. No existence
of a positive form or of an original equivalence is inferred. The completion
uses the supplied form's topology; no comparison with the original function
topology is asserted. Differential operators remain on the algebraic carrier:
there is no bounded extension or assertion of differential equivariance on all
completed vectors. Full archimedean globalization, smooth-vector recovery,
irreducibility, spectral occurrence and invariant integral formulas remain
separate obligations.
