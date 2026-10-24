# Spectral systems from actual presented unramified data

This internal construction connects the published `PresentedUnramifiedData`
and `Representation.Unramified.SpectralSystem` implementations. It introduces
no new assertion about the original literature.

## The forgetful construction

For a number field `F` and positive rank `r + 1`, let `P` be a genuine finite
tensor presentation onto a nonzero finite-adelic-invariant subspace of actual
automorphic forms. Such a subspace need not be finite dimensional. Given
`D : P.UnramifiedData hS T`, `D.spectralSystem` has exceptional set exactly
`T` and retains exactly the eigenvalue multisets supplied by `D`. The actual
data include local irreducibility, admissibility and normalized scalar action
of all standard spherical Hecke operators on the entire nonzero integral
fixed subspace outside `T`.

The forgetful map preserves the eigenvalues, every natural power trace, and
the Euler denominator polynomial by definitional equality. The theorem
`spectralSystem_hasSpectrum` retains the link to the actual embedded local
component: its whole-fixed-space scalar equations hold for the exported
eigenvalues. The normalization remains that of the imported actual data,
with integral subgroup Haar mass one and the positive-square-root residue
normalization in the standard Hecke scalar.

Restriction to a larger exceptional set commutes with this map as an equality
of spectral systems. Transport to another nonzero presentation of the same
full tensor family also gives an equal spectral system. The transport retains
the original factor representations, exceptional set and reference vectors;
it does not identify unrelated tensor families. The two restriction comparison
lemmas inherit the numerical relations for all positive power traces and
Euler polynomials. Together with the published symmetry and transitivity
laws, they allow enlargement of exceptional sets in comparisons.

## Finite families of actual data

`spectralSum` takes any finite type `J` of actual presentations and supplied
data, all over the same number field. The constituent ranks are independent
positive integers `r j + 1`; their carriers and actual target subspaces may
vary with `j`. The number-field, factor-carrier and family-index universes
are independent. No irreducibility of a combined global representation is
required or asserted.

The construction applies `SpectralSystem.finiteSum` to the exported systems.
Its exceptional set is their finite union, and the inclusion and
nonmembership lemmas expose each constituent's data at every retained
place. The multiset concatenation preserves every repeated eigenvalue and
every repeated family entry. Its rank is the sum of the constituent ranks.
The empty family is allowed and has rank zero.

The implemented proofs specialize the published finite multiset identities:
the power trace is the sum of the actual-data power traces, and the Euler
polynomial is the product of the actual-data Euler polynomials. The product
has natural degree exactly the sum of the positive constituent ranks,
including the empty-family case. No matrices, roots or spectra are chosen by
this construction.

The final equivalences expand comparison with any numerical spectral system
into the literal sum of actual-data traces or product of actual-data Euler
polynomials. One cofinite quantifier precedes all positive powers, so the
finite set of failures is uniform in the power. The other system may itself
be the exported data of another actual presentation or another finite family,
with different ranks and a different index type. The existing
`SpectralSystem.finiteSum_samePowerTraces_iff` and
`finiteSum_sameEulerPolynomials_iff` expand both families simultaneously.

## Scope and provenance

This is a construction from supplied spectral evidence on genuine actual
components. It does not establish existence or uniqueness of that evidence,
tensor factorization, Satake classification, cuspidal rigidity, an isobaric
automorphic realization of the numerical sum, arithmetic Frobenius data,
or weak global association. A numerical comparison with an arbitrary system
does not supply that system's missing arithmetic or automorphic realization.
Equality of the trace comparison and the Euler comparison remains a separate
algebraic obligation; the two final equivalences do not prove it.

All definitions and proofs derive from the two imported published modules.
The map and its compatibility equations reduce to their structure fields;
the family formulas use the finite-sum invariant identities; comparison
expansions compose those identities under the cofinite filter.
