# Supplied unramified spectra of presented automorphic components

This internal construction packages explicitly supplied spectra for actual
local components of a nonzero finite tensor presentation. It specializes the
published `LocalSphericalHecke`, `PadicLocalCategory` and
`Representation.Unramified.Eigenvalues` constructions. It makes no new
literature assertion.

## Data and conventions

Fix a number field `F`, positive rank `r + 1`, a family of complex
representations `ρ v` on spaces in an independent universe, and a genuine
`FiniteTensorPresentation P` onto a specified nonzero finite invariant
subspace `S` of actual automorphic forms. The tensor data include a finite
exceptional set `E` and nonzero integral-fixed reference vectors outside `E`.

`P.UnramifiedData hS T` requires a finite set `T` containing `E`. At every
finite place outside `T` it supplies irreducibility and admissibility of
`ρ v`, an unordered multiset of exactly `r + 1` nonzero complex eigenvalues,
and evidence of `HasSphericalHeckeSpectrum` on the actual embedded component
`P.localComponent hS v`. Admissibility retains the published smoothness and
finite-generation condition for every open subgroup.

The spectral evidence requires a nonzero integral fixed submodule and the
normalized scalar equation for every standard diagonal Hecke operator on
every vector of that submodule. The Haar measure gives the integral subgroup
mass one. The scalar convention is the existing
`sqrt(q)^(i*(n-i)) * (-1)^i * coeff_i(∏(1-αX))` with `n = r + 1`.
One eigenvector alone does not provide this evidence. The structure is data
conditional on these fields; no inhabitant is postulated.

## Actual classes and ambient forms

`hasSpectrumClass` identifies the supplied spectrum with the existing
spectral relation on the genuine p-adic class `P.localPadicClass`, using
exactly the irreducibility and admissibility stored in the data.
`isSphericalClass` specializes the proved nonzero integral-fixed-vector result
outside `E`, using `E ⊆ T`. The representative still has the actual
form-space carrier, in the field/form universe.

`exists_eigenform` extracts a nonzero ambient spherical Hecke eigenform by
the injective inclusion of the component's fixed submodule. The witness is a
vector of that submodule, so the included form belongs to the component.
This existence follows from the supplied whole-space spectral evidence.

## Numerical invariants and changes of presentation

`powerTrace v hv k` is the sum of the `k`th powers of the supplied
eigenvalues, counting every multiplicity. It is defined for all natural
powers, with zeroth value `r + 1`; unramified trace comparisons can quantify
over strictly positive powers. `eulerPolynomial v hv` is the product
`∏(1-αX)`, also counting multiplicities. It has constant coefficient one,
is nonzero, and has degree `r + 1`. These facts specialize the existing
multiset formulas.

`exists_matrix` supplies an actual invertible complex matrix whose reversed
characteristic polynomial and all natural power traces are these
invariants. The existing proof enumerates the multiset and uses a diagonal
matrix. This does not choose a canonical matrix or identify the matrix with
an arithmetic Frobenius.

`restrict` enlarges `T` by forgetting data at additional places; traces and
Euler polynomials at the remaining places are definitionally unchanged.
`transport` moves the supplied data to any other nonzero presentation of the
same tensor family, even when its target subspace differs. The proof first
passes to the genuine p-adic class, uses the published equality of those
classes, and returns to the new component's whole-space spectral relation.
The eigenvalue multiset, traces and Euler polynomials are unchanged.

## Scope

This construction proves no existence or uniqueness of spectra from
sphericality, fixed-space dimension, Satake classification, general tensor
factorization, uniqueness across different factor families, or arithmetic
association. In particular, two independently supplied data objects are not
asserted equal. The matrix trace/Euler equivalence and global rigidity
statements remain separate obligations.
