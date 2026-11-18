# Positivity restrictions for adding a leaf

`leafExtension N k a b` appends one vertex to the integral matrix `N`, with
diagonal entry two and nonzero links allowed only to the existing vertex `k`.
The entry from `k` to the new vertex is `a`; the reverse entry is `b`.
The old vertices retain their `Fin n` numbering and the new vertex is last.

The main internal lemma `leafExtension_positive_bound` assumes this extension
is finite Cartan, `a ≤ 0`, and a nonnegative integer vector `y` satisfying
`N *ᵥ y = c e_k` for a positive integer `c`. It proves
`0 < 2*c - a*b*y k`.

The proof extends `(-a) • y` by the new coordinate `c`. This is a nonzero
nonnegative integer vector. The extension matrix sends every old coordinate
to zero, while the last image coordinate is `2*c - a*b*y k`.
The positive-coordinate obstruction from the local structure proof forces
that last value to be positive.

This is an internal algebraic device for enumerating possible leaf
extensions of the standard finite Cartan matrices. It does not itself
classify those extensions.
