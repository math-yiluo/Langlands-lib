# Proof of discrete-series orbit finiteness in rank zero

`Langlands.HarishChandraSchwartz.rationalRankZeroDiscreteSeriesOrbitFiniteness`
proves the published statement
`Langlands.HarishChandraSchwartz.RationalRankZeroDiscreteSeriesOrbitFinitenessStatement`,
the rank-zero specialization of Waldspurger's Theorem VIII.1.2, with the
independent field and representation carrier universes `u` and `uV`. It
uses the published actual-point form of the counting argument of §VIII.5
with a coefficient bound that comes from compactness modulo the split
component.

## Compactness modulo the split component

`compactSpace_rationalPoints_quotient_of_relativeRootRank_eq_zero` shows
that the quotient of the actual rational point group by the image of any
split component is compact in the quotient topology.

Rank zero makes the relative-root span zero. Rationalization is injective
on the character lattice of the chosen maximal split torus, so every
relative root would have to be zero, and relative roots are nonzero.
Hence the torus has no roots, and the empty-root centrality theorem makes
it central on all scheme tests. It then factors through the given split
component, and maximality of the original torus makes the factor an
isomorphism. Thus the split component is itself maximal split.

The quotient group scheme by that component is connected reductive and
anisotropic, so its rational-point space is compact. The split-torus
quotient has local algebraic sections, which give the quotient topology
on rational points. The fppf kernel identity identifies the point
kernel with the image of the split component. The resulting
homeomorphism transfers compactness to the actual point-group quotient.

## Finite-dimensional fixed coefficients

`finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_of_compact_quotient`
works for any topological group `Γ`, central normal subgroup `A` with
compact quotient, character `χ` of `A`, Haar measure on `Γ ⧸ A` and open
subgroup `H`. It shows that the least fixed coefficient span
`discreteSeriesCentralFixedCoefficientSpace` is finite dimensional.

That span lies in the space of functions that transform by `χ` on the
left and are invariant under `H` on the right. For the character law,
apply the central action to each matrix coefficient of the chosen
irreducible representative. The open subgroup has open image in the
compact quotient, so its left coset space is finite. For an element `x`
of the group, let `r` lift the representative of its coset in that space.
Then `x = a * (r * h)` with `a` in the central subgroup and `h` in the
open subgroup. The value at `x` is `χ(a) * f(r)`. The finite tuple of
representative evaluations is therefore a linear injection.

## Conclusion

For a split component, a Haar measure on its quotient and a compact open
subgroup `H`, the published theorem
`finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional` reduces
finiteness of the unitary unramified twist orbits with a nonzero
`H`-fixed discrete-series member to one finite-dimensional space per
character, containing the `H`-bi-invariant coefficients. The proof
supplies `discreteSeriesCentralFixedCoefficientSpace` for every
character. Its membership lemma gives the containment, and the previous
section gives finite dimensionality. Continuity, unitarity and the
triviality of `χ` on `A ∩ H` are not needed for this space.

Waldspurger obtains the finite-dimensional space from Proposition VIII.4.1
for every semisimple rank. In rank zero the compactness of the quotient
gives it directly, so the proof does not use the induction on
semisimple rank.

See Waldspurger's Theorem VIII.1.2 and induction paragraph on printed
p. 321 (PDF p. 87), and the counting argument in §VIII.5 on printed
pp. 331–332 (PDF pp. 97–98). [Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)
