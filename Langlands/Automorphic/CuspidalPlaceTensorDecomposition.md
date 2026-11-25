# Tensor decomposition at the actual places of a cuspidal realization

This internal module specializes the finite-family compact and Lie tensor
construction to the actual local source subspaces and actual multiplicity spaces
of the Library's cuspidal operator realizations. Its provenance is the proved
`CuspidalArchimedeanDensityModels`, finite-factor evaluation and finite-family
tensor decomposition results. It is an algebraic ingredient for the global
Rankin–Selberg factorization, rather than a statement quoted from Cogdell.

The main proposition is
`Langlands.Automorphic.CuspidalOperatorRealization.PlaceTensorDecompositionStatement`.
The theorem `placeTensorDecomposition` proves it, without an open theorem premise.
For every number field with compact adelic quotient and every cuspidal operator
realization `T` of rank `r + 1`, it uses the existing choices
`A = T.finiteInfiniteDecomposition` and `D = T.placeDensityModels`. The first
choice is an actual nonzero irreducible admissible finite subrepresentation. The
second gives actual irreducible admissible source subspaces at all infinite
places, with their genuine restricted compact and Lie actions.

There is a complex linear equivalence

`E : (⨂[ℂ] i, D.subspace i) ≃ₗ[ℂ] A.InfiniteSpace`

which intertwines every local compact and Lie action in the pure-tensor sense
of `FiniteFamilyTensor.IsTensorEquivalence`. There is also a complex linear
equivalence

`e : A.finite.toSubmodule ⊗[ℂ] (⨂[ℂ] i, D.subspace i) ≃ₗ[ℂ] T.Space`

satisfying `e (a ⊗ₜ t) = E t a`. Here `A.InfiniteSpace` is the actual space
of finite-representation intertwiners into the realization, so `E t a` is
genuine evaluation, with all multiplicities retained. Rank `r = 0` is included.
The field universe remains free. These choices use no spectral-presentation
universe and do not identify the finite factor with a supplied spectral
presentation.

The construction is first implemented for an arbitrary operator realization
`S`, actual source data `D : S.PlaceDensityModels`, and a supplied finite
subrepresentation `A`. At this level the finite factor must be nonzero,
irreducible and admissible, and `S` must be irreducible.

`D.multiplicityTensorEquiv A ...` applies the finite-family tensor theorem to
the actual multiplicity action. Its hypotheses are discharged by:

- `D.densityHyp` for the actual source models;
- `finiteMultiplicityPlaceFamily_commutes` for the residual place actions;
- `finiteMultiplicityPlaceFamily_irreducible` for their joint irreducibility;
- `D.exists_nonzero_multiplicityHom` for a nonzero simultaneous compact and Lie
  occurrence of every chosen source in the multiplicity space.

It returns the equivalence together with both covariance properties.
`D.fullTensorEquiv A ...` tensors that equivalence with the identity on the
finite factor and composes with `finiteMultiplicityEquiv`. The latter is
actual evaluation. This gives `fullTensorEquiv_tmul` by definition.

The supporting theorems retain the three genuine actions needed by later
vector constructions. `fullTensorEquiv_finite` intertwines the finite adelic
action on the finite factor with `S.finiteRepresentation`.
`fullTensorEquiv_compact` and `fullTensorEquiv_lie` change only one component of
a pure infinite tensor. Their proofs evaluate the multiplicity covariance
identity at the fixed finite vector and use the defined residual actions.

`fullTensorEquiv_tmul_ne_zero` proves that a prescribed nonzero finite vector
and a nonzero infinite tensor have nonzero image. To prove nonvanishing of a
binary pure tensor, choose linear functionals taking the two vectors to one;
the tensor of those functionals also takes the pure tensor to one.
`fullTensorEquiv_pure_ne_zero` specializes this to an infinite pure tensor
whose components are all nonzero. Finiteness of the infinite-place index lets
one multiply normalized linear functionals on its components to obtain a
functional taking that dependent pure tensor to one. Injectivity of the full
equivalence then preserves nonzeroness. These arguments are algebraic and
claim no nonvanishing of a local or global integral.

Finally `T.allPlaceTensorEquiv` specializes the full construction to the chosen
cuspidal models. The theorem of the main proposition uses these choices and
their already proved irreducibility and admissibility properties.

This module imports `FiniteFamilyGKTensor` by Lean name. This module does not
compare these vectors with prescribed vectors in a supplied finite spectral
presentation; construct a simultaneous global Whittaker functional or its
ordinary and dual product formulas; extend compact and Lie covariance to
all infinite group elements; or prove archimedean integral nonvanishing. The
unconditional `ArchimedeanFactorizationStatement` remains open.
