# Reduction of Harris 1998, Theorem 1.2 in the cuspidal case

Author: Worker 773.

`Harris1998Theorem12CuspidalReductionStatement` is a conditional
proposition. Its conclusion is the published
`Langlands.GaloisRepresentation.Harris1998Theorem12CuspidalStatement`
with the same four universe parameters. This includes
`.{0, 0, uV, uV}` for each `uV`, as required by the Proposition 4.8
reduction. The conclusion uses the original CM compositum and
cuspidal hypotheses, and the original finite sum of pure families
of total rank `r+1` with weak association.

The premises are the two rank-one statements, the even-degree
geometric power endpoint, labelled Taylor extraction, regular
coefficient descent and their even-degree reduction. The odd-degree
reduction also takes the arithmetic supply of quadratic fields,
unitarity of the central character, the four automorphic comparison
inputs and their parity base-change reduction, quadratic patching
and its Frobenius comparison, absolute Frobenius density and the
finite coefficient model.
The final premise assembles these quadratic inputs using the even
output and the same regular coefficient descent. Each of these
premises is a named `Prop`.

For rank one, the determinant compares the spectrum to an algebraic
unitary Hecke character. Realize its Galois characters on the
coefficient lines and use the common rank-one eigenvalues and purity.
For rank at least two, split on the parity of `[E₀:ℚ]` and choose
a complex embedding of `E`. Apply the corresponding normalized
existence statement. The weights on the normalized polynomial are
the weight `r` of the arithmetic normalization, so replacing each root
by its unitary normalization removes the scalar `q^(r/2)` at good
places and gives the given spherical Euler polynomial. The collection
is pure and of rank `r+1`, and its weak association yields the
one-summand instance of the target, using
`isSumWeaklyAssociatedToSpectrum_unique_iff`.

This reduction retains the split square-integrable hypothesis in all
ranks. The 1993 doubling with a supercuspidal place is a separate
result. The construction takes all spectral comparisons at unramified
good places. Its use of one pure collection gives a witness to the
published existential sum.

## Provenance

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), Definition 1.1 and Theorem 1.2, and
  the unramified base-change comparison, pp. 183–186. Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- L. Clozel, 1991, §5.1, pp. 131–132, and Theorem 5.7, p. 142,
  for the arithmetic power convention and the CM good-parity case.
  Registered `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple
  Shimura Varieties* (2001), VII.1.9, pp. 227–232, for the even-degree
  construction, weights at a chosen embedding and the quadratic
  patching argument. Registered
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The implication combines these mathematical steps in the vocabulary of
the published target and the named inputs. It is an unproved statement
definition.
