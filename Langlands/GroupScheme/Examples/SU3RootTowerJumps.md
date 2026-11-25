# Indivisible coordinate jumps over finite henselian towers

This internal module begins with a value-group calculation for an
additive valuation on a field `L` and an embedded subfield `K`, in independent
universes. Assume that the nonzero embedded values lie in `(1/N) ℤ`, where
`N` is a positive natural number, and that some embedded value is one.

The positive numerators of attained base values form a nonempty set of
integers bounded below by zero. Choose its least element `m`, attained by
`π`, and put `c = m/N`. For any attained numerator `n`, multiplication by
`π ^ (-(n / m))` realizes the Euclidean remainder value `(n % m)/N`.
The remainder is nonnegative and smaller than `m`, so minimality forces it
to be zero. Every nonzero embedded value is therefore an integer multiple
of the attained positive value `c`.

This first arithmetic lemma imposes no characteristic, residue-field,
quadraticity, henselianity or completeness hypothesis.

For a separable quadratic extension `L/K`, `IsLatticeQuadraticValuation`
packages conjugation invariance, the above lattice containment for nonzero
embedded `K` values, and an attained embedded value one. Scaling the valuation
by `1/c` produces integer base values and an attained value one while
preserving conjugation invariance. It therefore satisfies
`IsNormalizedQuadraticValuation`. The normalized central-jump theorem and
positive-rescaling equivalence give an indivisible central coordinate jump
for the original valuation.

Finally, consider fields `k → E → L` in independent universes, with `E/k`
finite dimensional, `L/E` separable quadratic, and `L/k` separable. Let `k`
carry a surjective integer-valued valuation whose valuation ring is
henselian. Use its published original-base-normalized additive extension
valuation on `L`. Quadratic conjugation preserves that valuation. Since `L`
is finite dimensional over `k`, the norm lattice theorem puts every nonzero
embedded `E` value in `(1/[L:k]) ℤ`. Surjectivity on `k` supplies an attained
value one, viewed in `E` through the scalar tower. Thus
`tower_isLatticeQuadraticValuation` and `tower_hasIndivisibleCentralJump`
apply without any characteristic or residue-perfection restriction.

The final conclusion uses the literal coordinate jump sets: there is a real
central jump `r` such that `r/2` is absent from the ordinary quotient jump
set. The internal proof combines the published henselian extension and norm
valuation arithmetic with the normalized jump and rescaling modules.
Identification of these coordinates with actual root groups and transport
to every compatible apartment are not part of this module.
