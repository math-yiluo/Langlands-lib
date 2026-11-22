# Normalized infinite Whittaker slices over a totally complex field

Fix a totally complex number field with compact additive adelic quotient
and an actual cuspidal spectral presentation whose finite components are
irreducible and admissible. The adelic additive character is continuous,
nontrivial and unitary, and it is trivial on the diagonal field. At each
complex place `w`, the supplied standard parameter is `dC w` and the
nonzero scale `aC w` represents the restriction of this same adelic
character to that completion, as required by `IsComplexAdditiveComponent`.

The normalized `ModelData` map at `w` has range
`complexWhittakerModel r (dC w) (aC w)`. Identify each infinite tensor
factor with the compact-finite standard module for its parameter and
transport a normalized exact Whittaker map to that factor.

Fix a finite vector, the other infinite vectors, and the other group
arguments. The one-slot tensor insertion intertwines the compact and Lie
actions of the varying place. The fixed group arguments commute with that
place, so their evaluation on the insertion is an exact Whittaker
intertwiner. Complex Whittaker multiplicity one makes it a scalar multiple of
the normalized map. The same multiplicity-one theorem identifies the range
of the normalized map with the full specified local model. Total complexity
makes the real-place clauses vacuous.

This is an internal consequence of the Library's actual tensor equivalence,
standard coefficient equivalence, complex place covariance with frozen
arguments, and exact complex Jacquet multiplicity one.
