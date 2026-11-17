# Supplied root coordinates and dynamic root groups

This is internal derived content. It combines the existing represented dynamic
subgroups, supplied root parametrizations, actual field-fibre root coordinates,
and the published fibrewise isomorphism criterion. No new external-source
assertion is made.

Let `R` be any commutative ring, `G` an affine group scheme over `Spec R`, and
`i : G_m^I ⟶ G` a map from a finite coordinate split torus. Write `mu` and `nu`
for two integer cocharacters. The existing `dynamicCut i mu nu` is the
intersection, computed in `G`, of the dynamic centralizer of `mu` and the
positive dynamic subgroup of `nu`. The canonical `incl : Uc i mu nu ⟶ G`
first includes the unipotent dynamic group into the centralizer and then
includes the centralizer into an affine coordinate model of `G`.

`isClosedSubgroup_incl` proves that this inclusion is closed.
`isRepresentedBy_dynamicCut_incl` proves that it represents the actual
intersection on every test scheme. Its forward direction uses dynamic
functoriality; its reverse direction first factors a point through the
represented centralizer and then through its represented unipotent subgroup.
These results require neither smoothness nor a root datum.

Suppose a supplied `v : Ga R ⟶ G` is an `IsRootParametrization i a v`,
where the exponent `a` pairs to zero with `mu` and to a positive natural
number `d` with `nu`. The definition `rootToDynamic` factors this map
through `Uc i mu nu`, using the two existing root-containment lemmas.
`rootToDynamic_comp` states that composing it with `incl` recovers `v`.

Assume also `HasEquivariantFibres i mu nu a`: for every field equipped
with an `R`-algebra structure, the actual base-changed dynamic group has
an additive coordinate with the prescribed split-torus action on every
scheme test. `isIso_baseChange_rootToDynamic` compares the resulting
field root parametrization with the base change of `v`. Both represent
the same actual root subgroup. Uniqueness of representing objects gives
an isomorphism of their additive sources. Cancelling the represented
dynamic inclusion identifies the base-changed factorization with a
composite of three isomorphisms.

If `G` is smooth over `R`, `isIso_rootToDynamic` proves the factorization
itself is an isomorphism. The source `Ga R` and target `Uc i mu nu` are
smooth. Every residue-field pullback is an isomorphism by the preceding
field comparison; `isIso_of_residueField_fibres` therefore applies to the
underlying map over `Spec R`. The group isomorphism is recovered from
this underlying scheme isomorphism and the given group homomorphism.

`subgroup_eq_dynamicCut_of_parametrization` consequently identifies the
actual root functor with the dynamic intersection. Finally,
`isRepresentedBy_dynamicCut_of_parametrization` states that the supplied
`v` represents that intersection. These results apply to arbitrary rings,
including rings with nilpotents and the zero ring. They assume the
supplied root parametrization and equivariant fibres; they do not
construct a global root coordinate from fibre data alone.
