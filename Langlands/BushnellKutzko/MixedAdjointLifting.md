# Mixed adjoint lifting

`exists_mixed_adjoint_lift` develops the part of Bushnell–Kutzko
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Proposition
(1.4.16), printed pages 42–43, used for the two invertible multipliers
in the simple intertwining theorem. The inputs include a chain over
the extension field \(E\) with the same lattice subsets as the base
chain, linearity over \(E\) of the adjoint kernel, and single-step
adjoint lifting at the fixed depth offset \(k\).

The proof chooses a common splitting basis for the output chain and
its translate by the left multiplier. It chooses a common input
basis for the original chain and its translate by the inverse of the
right multiplier. On these bases each coordinate block is an
endomorphism of \(E\) over the base field. Projecting to a block
commutes with the adjoint map because the element defining the
adjoint acts by the same scalar on every coordinate line.

For two chains with the same period, the condition on one block mapping
the source chain to the target chain at a given depth is an inequality
on the uniformizer orders of the input and output scalars. The chain
and depth enter as a single integer threshold. In a sum of translated
lattice steps, this lets one assign the entire block to a summand
having the least threshold. For an adjoint in the sum, each assigned
block is still an adjoint. Undoing the translations lets the proof
apply single-step lifting to each of the three resulting terms.

To ensure that the preimages also sum into the required original
lattice step, the proof subtracts from each translated preimage the
\(E\)-linear map with the same values on the input basis. The subtracted
map has zero adjoint and preserves the lattice mapping conditions
because the chains have a common period. The sum of the three
corrected preimages is the original endomorphism after the same
subtraction, since the original difference is in the adjoint kernel.
This gives the desired depth and adjoint value for the sum, and the
individual preimages retain their specified depths and adjoint depths.

`exists_relative_corrections` uses the same interpolation for a linear equation
`(1 + a) z = y (1 + b)` with relative automorphisms `y` and `z`. If `a` and
`b` have the given base lattice depth, it gives relative endomorphisms `a'`
and `b'` at that depth with `(1 + a') z = y (1 + b')`. Choose a common
splitting basis for the relative chain and its translate by `z⁻¹`, and
interpolate `az` and `b` on that basis. Multiplying the interpolant of `az`
on the right by `z⁻¹` restores the original lattice condition. Equality on
the basis proves the equation between the relative maps. This supplies the
linear step for the relative double cosets in BK93 (1.6.1), printed p. 47
(PDF p. 59).
