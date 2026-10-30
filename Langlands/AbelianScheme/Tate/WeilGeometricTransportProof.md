# Geometric path compatibility of the actual rational Weil pairing: proof

`Langlands.AbelianScheme.rationalWeilGeometricTransport` proves the
published proposition
`Langlands.AbelianScheme.RationalWeilGeometricTransportStatement`, unchanged.
The module adds no definitions; it contains only the auxiliary lemmas
below and the final theorem. Every hypothesis of the statement stays an
explicit input. In particular, the relative finite Weil transition
proposition, the torsion finite-étaleness statement and the finite
étaleness of the selected roots-of-unity schemes are used as given, never
proved here. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The argument is the one the statement suggests: naturality of path
evaluation applied to the finite pairing morphism, then passage to the
inverse limit and rationalization. It is an internal deduction from the
Library's constructions and has no separate literature source; the
mathematical motivation is the Galois equivariance of the Weil pairing
cited in the statement's Markdown.

## Products of finite étale covers

A path `p` acts on the points of finite étale objects over `S` through
`pathAct`, and the published `pathAct_naturality` shows that this action
commutes with composition by any morphism between such objects. To apply
it to the finite pairing, whose source is the binary product of two torsion
kernels in `Over S`, the product must itself be finite étale.

- `FiniteEtale.prod_hom_eq_pullback` writes the structure morphism of
  `Y ⨯ Z` as `Over.prodLeftIsoPullback` followed by the pullback projection
  and `Y.hom`.
- `FiniteEtale.prod_isFinite` and `FiniteEtale.prod_etale` deduce that
  this composite is finite, respectively étale, when `Y` and `Z` are. They
  are only local instances in this file and are not registered globally.
- `FiniteEtale.pathAct_prodLift` shows that path evaluation of
  `prod.lift x y` is `prod.lift` of the evaluations: both projections are
  compared through `pathAct_naturality`.
- `FiniteEtale.pathAct_prodLift_comp` then gives, for any morphism
  `q : Y ⨯ Z ⟶ W` of finite étale objects,
  `pathAct p W (prod.lift x y ≫ q) = prod.lift (pathAct p Y x) (pathAct p Z y) ≫ q`.

## Finite level

`GroupScheme.mu.levelMap_pointsLevelEquiv` records the definitional
equality between the root on `Γ(Spec Ω, ⊤)`, sent to `Ω` by
`TateTwist.levelMap` along `ΓSpecIso`, and the affine root
`mu.levelEquiv n s` of the same `μ_n`-point.

`GroupScheme.Tate.levelTransport_kernelPairing` is the generic finite-level
step. It holds for commutative group objects `G`, `H` whose `n`-torsion
kernels are finite étale, and for an arbitrary morphism
`q : ker[n]_G ⨯ ker[n]_H ⟶ μ_n` with `μ_n` finite étale. The proof writes
both level elements as kernel points through `kernelLevelEquiv` and
rewrites the finite level transports with
`GroupScheme.Tate.finiteLevelTransport_kernel`. It rewrites the root
transport with `TateTwist.Geometry.levelTransport_kernel` and identifies
the resulting kernel points with `pathAct_prodLift_comp`.

`AbelianScheme.levelTransport_finiteWeilLevelBilinearMap` specializes this
to `G = A`, `H` the constructed dual `DA`, and `q` the actual
`finiteWeilPairing`. It uses the published application formula
`finiteWeilLevelBilinearMap_apply`. The finite étaleness of both torsion
kernels comes from `Tate.torsionKernel_isFinite` and
`Tate.torsionKernel_etale`, applied to the given torsion statement with
the positivity and invertibility of `n`. With these instances,
`Tate.levelTransport` is definitionally the generic finite level transport.

## Integral, rational and pulled-back pairings

`AbelianScheme.integralTransport_integralWeilBilinearMap` compares the
integral pairings coordinatewise. Elements of the twist inverse limit are
equal when all their coordinates at the selected orders are, and each
coordinate is the finite-level equality above.

`AbelianScheme.sectionRationalTransport_rationalWeilBilinearMap` is the
first conclusion. Unfolding `sectionRationalTransport` and moving the
inverse section-ring comparison at `t` to the other side, it suffices to
compare elements of the rationalized twist over `Ω'`. Both sides are
additive in each argument, so tensor induction on `ℚ ⊗ Integral` reduces to
pure tensors `q ⊗ x` and `r ⊗ y`. On those, `rationalWeilBilinearMap_tmul`,
`Tate.rationalTransport_tmul`, `sectionRationalEquiv_apply`,
`Divisibility.rationalMap_tmul` and `TateTwist.Geometry.rationalTransport_tmul`
reduce the two sides to `(q * r) ⊗ₜ` the path transport of the integral
value at `s`, respectively `(q * r) ⊗ₜ` the integral value at `t` of the
transported arguments, both read in the twist over the point fields. These
agree by the integral lemma.

`AbelianScheme.sectionRationalTransport_rationalWeilAlongHomBilinearMap` is
the second conclusion, for every homomorphism `lam : A ⟶ DA`. By
`rationalWeilAlongHomBilinearMap_apply` the pulled-back pairing is the
rational pairing with the rational Tate map of `lam` applied to its second
argument. The first conclusion handles the pairing, and the published
naturality `Tate.rationalTransport_map` moves the path transport past the
map induced by `lam`. No polarization hypothesis is used.

`rationalWeilGeometricTransport` introduces the statement's binders and
packages the two conclusions.

## Scope

The proof uses the actual constructed pairing, dual abelian scheme, path
maps and section-ring twist transport. It assumes no pairing compatibility
and replaces none of these objects by equivariant data. It does not prove
that a path exists, that the pairing is alternating or nondegenerate, or
any of the explicit hypotheses of the statement.
