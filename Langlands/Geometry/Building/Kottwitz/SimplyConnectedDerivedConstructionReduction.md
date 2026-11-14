# Construction through an actual cocenter

This internal reduction implements the formal construction in Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), §11.5 before Lemma 11.5.1
(printed pp. 429–430, PDF pp. 460–461). The registered 1 November 2024
corrections change §11.7 and do not alter this passage. The declarations are
derived helpers, rather than an unconditional proof of the source's construction.

`cocenterKottwitzCandidate` composes the actual quotient on points and selected
torus Kottwitz homomorphism with the inverse of a bijective cocenter target map.
`cocenterKottwitzCandidate_law` verifies its actual cocenter square, and
`exists_cocenterKottwitzLawAt` records existence.
`eq_of_cocenterKottwitzLawAt` proves uniqueness from a single actual cocenter
square when its target map is injective.

`cocenterKottwitzLawAt_of_torus_naturality` transports one square to another
actual cocenter of the same group. It applies the published conditional target
naturality theorem to the identity of the group, uses the identity law of the
fundamental inertia map, and then uses torus naturality for the actual induced
map of cocenters and its quotient factorization.

`simplyConnectedDerivedKottwitz_of_cocenter_data` proves all the conclusions of
`SimplyConnectedDerivedKottwitzStatement` at a fixed field tower and group under
the following explicit inputs:

- the algebraic fundamental comparison and map statements, torus fundamental
  comparison statement, fundamental inertia map statement and torus inertia
  comparison statement;
- bijectivity of every actual cocenter target map;
- naturality of the selected torus Kottwitz homomorphisms for the actual maps
  from one supplied cocenter to every other cocenter;
- surjectivity of the composite of that cocenter quotient on actual
  `UnramifiedClosure F` points and its selected torus Kottwitz homomorphism.

The proof first constructs a square at the supplied cocenter, transports it to
all cocenters, and proves unique existence. The epsilon specification then gives
the characterization of the selected simply-connected-derived homomorphism.
Surjectivity follows by lifting the image of a desired target element through
the assumed surjective composite and using target injectivity. The final
equivalence follows from uniqueness at each individual cocenter.

The theorem retains the integral inertia targets, including torsion. It assumes
surjectivity only of the composite with the torus Kottwitz homomorphism; it does
not assume point surjectivity of the cocenter quotient. The remaining inputs
are genuine mathematical obligations and are not discharged by this reduction.
