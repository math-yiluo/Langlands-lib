# Local central-kernel representations from jet representations

This internal module proves
`Langlands.GroupScheme.LocalCentralKernelRepresentationStatement`
conditionally on two statements taken as hypotheses:

- `JetCentralizerStabilizationStatement`: over an affine base, a smooth,
  separated, quasi-compact group with connected residue fibres has an order
  `n` such that every point centralizing the order-`n` identity jet is
  central (SGA 3, Exposé XI, 6.11(b));
- `JetConjugationRepresentationStatement`: for every `n`, every point of the
  base has arbitrarily small affine open neighbourhoods over which conjugation
  on the order-`n` jet is a matrix representation with kernel exactly the jet
  centralizer (SGA 3, Exposé XVI, 3.1).

It adds no geometric input beyond the compatibility of identity jets with base
change.

## Jets of a separated group under base change

Fix a group scheme `G` over `S` with separated structure morphism and a base
change `b : T ⟶ S`.

- `IdentityJet.isClosedImmersion_identitySection`: the unit section is a
  closed immersion, because its composite with the separated structure
  morphism is the identity.
- `IdentityJet.ideal_baseChange_of_isSeparated`: pulling back the order-`n`
  jet ideal along the projection `G_T → G` gives the order-`n` jet ideal of
  `G_T`. The proof copies the Library's `IdentityJet.ideal_baseChange`. That
  theorem assumes `G` affine over `S`, but uses this only to make the unit
  section a closed immersion. The ideal of the base-changed unit section is
  the pulled-back ideal (the unit-section square is cartesian), and pullback
  of ideal sheaves commutes with powers (`IdentityJet.idealSheaf_comap_pow`).
- `IdentityJet.jetBaseChangeMap` and
  `IdentityJet.jetBaseChange_isPullback`: the base-changed jet maps to
  the jet, and the square formed with the two jet inclusions and the
  projection `G_T → G` is cartesian. Both jet inclusions are closed
  immersions, so this follows from the ideal equality.
- `IdentityJet.isJetPoint_baseChange_iff`: a point `x` of `G_T` is a jet
  point exactly when its image under `baseChangePointsEquiv b G` is a jet
  point of `G`. Composing with the jet map gives one direction. The
  cartesian square gives the other.
- `IdentityJet.CentralizesJet.comp`: centralizing a jet is stable under
  restriction to any morphism of test schemes.
- `IdentityJet.CentralizesJet.of_baseChange` and
  `IdentityJet.CentralizesJet.baseChange`: a point of `G_T` centralizes the
  jet of `G_T` exactly when its image centralizes the jet of `G`. For the
  first, a refinement `V' ⟶ U'` of the image test scheme is rewritten as the
  image of a test scheme over `T` through an isomorphism with identity
  underlying morphism. The point equivalence is multiplicative and natural,
  so commutation transfers. The second direction uses naturality and
  injectivity of the point equivalence.

## The conditional theorem

`localCentralKernelRepresentation_of` proves the target from the two
hypotheses. Let `G` over `S` be smooth, separated and quasi-compact with
connected residue fibres, and let `s : S`.

1. Choose an affine open `W ∋ s`, with `i₁ : Spec Γ(S, W) ⟶ S`, and put
   `G₁ = G_{i₁}`. It is smooth, separated and quasi-compact. Its residue
   fibres are connected by the Library's
   `ExtensionReduction.connectedSpace_residueFiber_baseChange_iff`. The
   stabilisation statement gives an order `n` for `G₁`.
2. The representation statement with this `n` and the neighbourhood `W`
   gives `i : Spec R ⟶ S` with image in `W` and a representation `ρ` of
   `G_i` whose kernel is the jet centralizer.
3. Let `g` be a point of `G_i` on `U` with `g ≫ ρ = 1`. It centralizes the
   jet of `G_i`, so its image centralizes the jet of `G`. The test scheme
   `U → S` factors through `i₁` (`IsOpenImmersion.lift`), so this point
   comes from a point `g₁` of `G₁` that centralizes the jet of `G₁`. By
   step 1, `g₁` is central. Transporting back through the point
   equivalences and the comparison isomorphism of test schemes shows that
   `g` commutes with every point of `G_i` on `U`.

The representation `ρ` of step 2 is therefore the one required. The theorem
does not prove either hypothesis. They are proved separately, by
`jetCentralizerStabilization_of_centerDetection` (`IdentityJetCentralizerComparison`)
and by `jetConjugationRepresentation_of identityJetLocallyFree`
(`IdentityJetRepresentation`).
