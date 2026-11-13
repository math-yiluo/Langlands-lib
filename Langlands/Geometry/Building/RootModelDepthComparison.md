# Reduction compatibility from deeper integral root models

This is derived infrastructure for the supplied-model lifting construction in
`SmoothRootModelLifting`. It proves a sufficient geometric condition for
`RootModelReductionCompatible`. It asserts no existence of root models, no
comparison with an unramified building, and no theorem of root-jump descent.

## Actual comparison data

Fix a Henselian local domain `R`, its fraction field `K`, a commutative group
scheme `S` over `K`, group schemes `G` and `U` over `K`, homomorphisms
`i : S.toGrp ⟶ G` and `j : U ⟶ G`, a character `a`, a raw root-function
family `φ`, an actual integral model `M` of `U`, and a homomorphism
`q : M.specialFibre ⟶ Q` over the residue field.

`RootModelDepthComparison i a j M φ q r` supplies an actual generic group
`V`, a homomorphism `f : V ⟶ U`, an actual integral model `N` of `V`, and an
integral-model morphism `N.Hom M f`. Thus the generic square commutes with the
models' supplied generic-fibre identifications. Its two further requirements
are:

- The image of `N.integralPoints` under the actual generic map `f ≫ j`
  is exactly the raw filtration set `rootFiltration i φ a r`.
- The actual composite from `N.specialFibre` to `M.specialFibre` and then to
  `Q` is the identity-valued morphism. The equality is of scheme morphisms
  over the residue field, so it holds on all test schemes.

No smoothness, connectedness, reductivity or valuation axiom is imposed on the
comparison data. The integral-model definition already requires affine, flat,
finite-type models.

## Implemented proofs

`RootModelDepthComparison.exists_section` assumes that the underlying morphism
of `j` over `K` is a monomorphism. If an integral section `x` of `M` has
ambient generic point in the filtration at depth `r`, the exact image equality
provides an integral section `y` of `N` with the same ambient generic point.
Generic naturality of the actual model morphism and cancellation of `j`
identify their generic points in `U`. The published injectivity of
`M.integralPointMap` then identifies the integral sections.

`RootModelDepthComparison.quotientReduction_eq_one` applies this section lift,
reduction naturality, and the scheme-level identity-valued composite to prove
`q(M.reduction x) = 1`.

`HasCofinalRootModelDepthComparisons` is the proposition that for every real
`ε > 0` there exists a real `r` with `0 < r ≤ ε` admitting actual comparison
data. It is an explicit input rather than an existence result.

`rootModelReductionCompatible_of_depthComparisons` assumes that `j` represents
the actual generic root subgroup, that the image of `M.integralPoints` under
`j` equals the depth-zero filtration, and that these cofinal positive-depth
comparisons exist. Depth-zero membership supplies both actual root membership
and nonnegativity for every integral section. Given a strictly positive value
in `WithTop ℝ`, order density supplies a finite real `ε > 0` below it, including
when the value is infinity. Choose a comparison depth `r ≤ ε`. The section
belongs to the filtration at `r`, so the preceding lemma kills its reduction
in `Q`. These are exactly the two clauses of
`RootModelReductionCompatible`.

## Provenance and remaining obligations

The proof is an internal consequence of the published integral-model
injectivity and naturality lemmas and the definition of the raw root
filtration. It uses no additional literature theorem. Its use in unramified
descent still requires constructing the models and their compatible
morphisms, proving both exact filtration image equalities and the
identity-valued residue composites, and constructing the required residue
quotient and root comparison. None of these existence or comparison
obligations is discharged here.
