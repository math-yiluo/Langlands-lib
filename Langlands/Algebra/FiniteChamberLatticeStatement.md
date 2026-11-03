# Finite orthant coordinates modulo the kernel of the root pairings

`Langlands.FiniteChamberLatticeStatement` is an internal algebraic reduction for
the finite chamber coordinates used in the general rational square-integrability
argument. The finite coordinate type and additive-group universe are independent.

Let `X` be an additive commutative group and let `pair α : X →+ ℤ` be an integral
pairing for each member of a finite type `Δ`. Assume that every finite subset `I`
admits a vector whose pairings vanish on `I` and are strictly positive outside
`I`. There is then a family `gen α` with positive `α` pairing and zero pairing
with every distinct label. These generators are chosen once, independently of
the chamber bound.

For every integer `B`, there is a finite set `R` such that each `x` with
`pair α x ≥ -B` for all `α` is

`x = r + ∑ α, n α • gen α + z`,

where `r ∈ R`, each `n α` is a natural number, and every pairing vanishes on `z`.
No freeness, finite generation or injectivity assumption is imposed on `X`.
The assertion includes an empty coordinate type and chamber bounds of either sign.

The internal derivation chooses `gen α` by applying the hypothesis to all
labels other than `α`. Euclidean division of `pair α x + B` by
`pair α (gen α)` gives the natural coordinates. The remainders lie in a finite
product of integer intervals. Choose one vector for each attained remainder
tuple; subtracting its representative leaves the common kernel.

The standard-cocharacter premise is precisely the algebraic premise already
present in `IsCartanLatticeModel.exists_standard`. The new assertion isolates
its finite orthant consequence. Applying it to an actual reductive group still
requires the actual lattice model, comparison of the pairing kernel with
central elements, and the Cartan covering. No group compactness, Haar volume
bound, coefficient estimate or square-integrability conclusion is asserted here.
