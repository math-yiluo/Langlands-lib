# Rational evaluation of Galois-transported cocharacters and coroots

Provenance: internal. This module converts the published affine cocharacter
transport formula to the actual rational-point convention used in
`EvenChainPatternProducts`. It is a helper for the even-chain Galois-data proof.

`rationalCocharacterValue` evaluates an actual cocharacter of the base changed
group at a field unit. Applying `baseChangeCoeffEquiv` gives exactly the existing
`affineCocharacterValue`. The general conjugation theorem follows from
`affineCocharacterValue_transport` in `CocharacterAffineTransport`, using the
injectivity of this comparison. The inverse field automorphism in that formula
cancels the automorphism applied to the unit in the rational-point conclusion.

For a commutative group scheme `T` and a ground-field map `i : T.toGrp ⟶ G`,
`cocharacterLattice.rationalValue_galoisRepresentation` applies this formula to
an ordinary Galois-transported cocharacter of `T_K` followed by the base change
of `i`. The proof uses `transportCocharacter_naturality` and the definition of
the cocharacter-lattice Galois action.

For a supplied split pinning and a supplied identification `eT` of its torus
and inclusion with this descended torus and inclusion, `corootHom_congr`
identifies the two presentations of the actual coroot map. The last theorem
shows that a supplied coroot-lattice transport equality implies
`σ(α∨(t)) = β∨(σ(t))` for the actual rational values. It rewrites to the
preceding lattice evaluation theorem. The last theorem retains its explicit
coroot-lattice equality premise; this module does not deduce it from a root
transport equality or assert existence of compatible even-path data.

The fields lie in one arbitrary universe. No finite-degree, Galois-extension,
characteristic, perfection, infinitude or simple-connectedness premise is needed:
an individual algebra automorphism is sufficient. The group in the general
cocharacter statements need not be affine; the pinning specialization has the
affineness needed by `SplitPinning`.
