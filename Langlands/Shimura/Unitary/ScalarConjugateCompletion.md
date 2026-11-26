# Localization of scalar conjugates

`scalarConjugateCompletionEquiv` identifies the completed scalar
conjugate of a central simple algebra with the scalar extension of
the original algebra from the corresponding conjugate completion. The
isomorphism of the two actual completed fields intertwines the two global
embeddings through the scalar automorphism. Tensoring that semilinear map
with the identity on the underlying ring, viewed as a semilinear map to
the scalar twist, gives the ring chart. Scalar extension along the
completed field isomorphism makes this an equivalence of algebras over
the target completion.

`finiteBrauerInvariant_scalarConjugate` uses continuity and valuation
preservation of the completed field isomorphism to compare finite
invariants. `classOf_eq_of_finiteBrauerInvariants` applies the number
field Brauer splitting theorem to the difference of two central simple
algebras over a totally complex field. Their finite invariants cancel and
the archimedean completions are algebraically closed.
