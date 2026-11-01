# Nonvanishing of the actual adjacent Jacquet functional

This is an internal derivation for the actual canonical normalized opposite
parabolic induction with ordered blocks `(r+1,1)`. It constructs a compact
local section on which the scalar Jacquet integral is nonzero. The original
representation `sigma` acts on an arbitrary complex module `V` in the
independent universe `uV`; no topology, norm, irreducibility or injectivity of
its coefficient map is assumed. Every natural `r`, including zero, is allowed.
The field carries its canonical p-adic topology and Borel structure.

The result `AdjacentJacquet.functional_ne_zero` applies to an arbitrary
continuous quasicharacter `chi` and the supplied scalar additive Haar `nu`.
Its hypotheses are smoothness of `sigma`, nonvanishing of the specified
standard Whittaker functional `ell.val`, and the explicitly quantified
all-section integrability hypothesis required by
`AdjacentJacquet.functional`. That last hypothesis is conditional here:
the host proof must discharge it at sufficiently large real twists. This
module establishes neither the uniform convergence threshold nor the whole
tensor-integral image equality.

The definition `AdjacentJacquet.nonzeroFunctional` bundles the same
`functional` with this nonvanishing proof, as a member of the subtype of
standard Whittaker functionals whose underlying linear maps are nonzero.
Its underlying functional is definitionally the earlier scalar integral
functional, so all existing coefficient identities apply to it.

## Exact upper-column coordinates

`columnCoordinate` extracts the entries above the last diagonal entry of
an ambient matrix. It is a continuous left inverse of the literal
`upperColumn x = [I,x;0,1]` used by the scalar Jacquet kernel. The module
proves that these matrices lie in the upper radical for the exact lower
shape, and conversely that each member of this radical is the upper
column extracted by `columnCoordinate`. These are direct entrywise matrix
proofs with the fixed block indices. The upper-column map is continuous
and sends zero to the identity.

`inducing_isSmooth` proves smoothness of
`Padic.adjacentRankLowerTensorRepresentation F sigma chi`. This is the
exact inducing action on
`PiTensorProduct C (Shahidi.pairCarrier V (ULift C))`.
The proof uses smoothness of both block factors, smoothness of their finite
external tensor product, continuous pullback along the opposite Levi
projection, and the open kernel of the normalizing half-modulus twist.

`phase_eq_one_neighborhood` supplies an open neighborhood `O` of the zero
column on which `psi.complex (-x_last) = 1`. The continuous character
of the multiplicative type wrapper of the additive field has open kernel
by `isOpen_ker_of_continuous_complex_character`. Pulling that kernel back
by the negative last coordinate gives `O`. This does not require
nontriviality of `psi`.

## Compact local section

`exists_constantKernel_section` proves that, for every `v : V`, there are
an open compact column set `L` containing zero and an actual section `f`
of `inducedRepresentation F sigma chi` such that

```text
integrand F psi sigma ell chi f 1 = L.indicator (fun _ => ell.val v).
```

This is equality of functions on the entire column space.

The vector at the identity is
`z = (adjacentRankLowerTensorCoordinates V).symm v` in the original
tensor carrier. Smoothness gives an open lower-parabolic subgroup `H`
fixing `z`. Choose an ambient open set whose intersection with the
parabolic is `H`, and intersect it with the inverse image of `O` under
`columnCoordinate`.
`BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization`
supplies a compact open subgroup `K` contained in this neighborhood.
Consequently `P intersect K` fixes `z`.

Set `L = upperColumn` inverse image of `K`. It is open and closed.
It is compact because it is a closed subset of the continuous image
`columnCoordinate(K)`, and it contains zero. The choice of `K` also
ensures `L` is contained in `O`.

Use the existing
`Induction.compactDoubleCosetSection P tau K hKc 1 z hz`.
Its restriction to upper columns in `K` has value exactly `z`.
For the complement, its quotient support and the block Iwahori
factorization show that any upper column with nonzero section value
would factor as `q*n` with `q` in the lower parabolic and `n` in
the upper radical intersected with `K`. Since the upper column and `n`
lie in that radical, so does `q`. The existing
`eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup` forces `q=1`,
placing the original column in `K`. This contradiction proves the
section vanishes on every column outside `L`.

Applying the original tensor-coordinate equivalence and `ell.val`
therefore gives the constant `ell.val v` on `L` and zero outside it.
The negative Jacquet phase is one on `L` by its containment in `O`.
This proves the displayed identity for the actual scalar kernel.

## Nonzero value with the supplied Haar

Choose `v` with `ell.val v` nonzero and take the preceding section.
Write `mu = rowMeasure nu (r+1)`, retaining the caller's scalar Haar.
Openness and the zero member give `0 < mu L`; compactness gives
`mu L < infinity`. Hence `mu.real L > 0`. The existing integral formula
for an indicator of a constant gives

```text
(functional F psi sigma ell chi nu hI).val f
  = (mu.real L : C) * ell.val v,
```

which is nonzero. Thus the single standard Whittaker functional
previously constructed from the actual Jacquet integral has nonzero
underlying linear map. No choice of Haar normalization or self-duality
certificate is needed for this nonvanishing argument.

## Provenance

The construction adapts the elementary compact double-coset argument in
`RankOneExtensionCompactSectionProof.exists_rankOneExtensionCellSection`
to the exact adjacent shape and tensor carrier. It uses the published
`CompactLocalSection`, `OppositeBlockIntersection`, and
`BlockIwahoriBasis` constructions directly. Unlike that general helper,
the present proof needs no second ambient representation to stabilize
and no volume-normalized test function. Its value is simply the positive
volume of `L` times the specified original functional value.
This is an internal derivation from these Library constructions,
finite matrix identities, smoothness, the open character kernel, and
the scalar Haar integral of a constant indicator.
