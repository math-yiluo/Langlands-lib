# Spanning by integrated conjugate coefficient cutoffs

This is an internal derivation from the actual supercuspidal coefficient cutoffs,
the compact integrated action, and Haar conjugation symmetry. It supplies a
spanning step for extending identities from smoothed matrix tests; it does not
assume or establish a functional equation.

For a canonical p-adic field and a supercuspidal representation of GL of rank
`m + 1`, let the compact group test be the complex conjugate of the coefficient
`g ↦ ℓ(ρ(g)v)` cut off to determinant norm one. The functional `ℓ` is smooth for
the algebraic dual action. Acting by `a` on both `ℓ` and `v` gives the old test at
`g` when the new test is evaluated at `a g a⁻¹`. The determinant norm is unchanged
by conjugation. Measure preservation of inner conjugation and naturality of the
finite-fiber integral therefore show that acting by `ρ(a)` on an integrated
output gives another output of the same family.

If `ℓ(v) ≠ 0`, applying `ℓ` to the integrated test acting on `v` gives the complex
embedding of the integral of the squared norm of the cutoff coefficient. The
coefficient is continuous with compact support and is nonzero at the identity,
so this real integral is strictly positive. The integrated output is nonzero.

`supercuspidalCutoffOutputSpan` is the complex span of all these outputs, allowing
every smooth dual functional and both input vectors. Its action stability follows
from the conjugation formula. If the representation is irreducible, the span is
the whole carrier: the associated subrepresentation is either bottom or top;
in the bottom case smooth functionals separating any nonzero vector and the
positive integral would contradict each other, so the carrier is trivial and its
span is again top. Field and representation universes remain independent. No
topology on the representation space, additional admissibility assumption, or bound
`0 < m` is needed.
