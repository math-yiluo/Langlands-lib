# Canonical Jacquet lift naturality under representation intertwiners

`Langlands.Jacquet.canonicalLiftIntertwinerNaturality` proves the exact closed
proposition `Langlands.Jacquet.CanonicalLiftIntertwinerNaturalityStatement`.
The group universe and the two representation-carrier universes remain
independent. The theorem quantifies over every topological group, smooth
complex representations `rho` and `sigma`, compact open subgroup `K`, group
element `g`, and actual intertwiner `f` from `rho` to `sigma`.

The proof is internal derived linear algebra on the existing constructions in
`CanonicalLiftDefinitions` and `Coinvariants`. It does not translate a separate
literature theorem. The imported statement and its constructions are unchanged.

## Preservation of the all-power stable image

`compressedAction_pow_natural` proves by induction on `r : Nat` that the
fixed-vector map induced by `f` commutes with the `r`th powers of the two
compressed actions. The zero case is reflexivity. In the successor case,
`compressedAction_natural` commutes with the outer action, and the induction
hypothesis commutes with the preceding power.

`fixedVectorsMap_mem_stableImage` expands membership using `mem_stableImage`.
For each natural power, membership supplies a preimage `w` of the source
vector. The image of `w` under the fixed-vector map is a preimage of the image
vector, by the power identity. This proves preservation of the intersection
of all power ranges, including the zeroth power, without a stabilization
assumption.

## Naturality of the actual Jacquet quotient

`fixedJacquetMap_natural` applies for arbitrary subgroups `N` and `M` with
`M` normalizing `N`. The source fixed subgroup is `K`, and the quotient fixed
subgroup is `K.comap M.subtype`. Subtype extensionality reduces the asserted
fixed-vector equality to its underlying coinvariant classes.
`Jacquet.map_mk`, in the reverse direction, identifies both classes with the
class represented by `f(v)`. The quotient action here is the existing
unnormalized descended action.

## Naturality of the inverse lifts

`inverseCanonicalLift_natural` retains the two explicit bijectivity hypotheses
on the actual `stableImageJacquetMap` maps. Let `u` be the source inverse lift
of the fixed quotient vector `j`, using exactly the inverse of
`LinearEquiv.ofBijective`. Its source restricted quotient is `j` by
`apply_symm_apply`.

The fixed-vector image of `u` lies in the target stable image by the first
helper. Call this stable-image element `w`. The quotient square just proved
shows that the target restricted quotient of `w` is the fixed-vector image of
`j` under the actual `Jacquet.map`. The target inverse lift has the same
restricted quotient by `apply_symm_apply`. Injectivity of the target
restriction therefore identifies `w` with that inverse lift. Applying the
existing inclusion `stableImageToRepresentation` gives the required equality
of actual vectors in the target representation.

The final theorem introduces the full statement telescope and combines these
three results. Bijectivity is used only in the final inverse-lift clause.
There is no assumption that `f` is injective, surjective, or an isomorphism,
and no admissibility or finite-dimensionality hypothesis. The result proves
neither stabilization nor bijectivity of the restricted quotient maps.
Global Jacquet duality, the generic multiplicity comparison, and the
irreducible-head consequence remain separate obligations.
