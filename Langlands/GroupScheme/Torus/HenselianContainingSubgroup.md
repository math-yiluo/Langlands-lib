# Henselian residue-torus lifts containing a prescribed split torus

`Langlands.GroupScheme.HenselianTorusLifting.containingLiftData` refines the
published exact residue-torus lift with containment of a specified integral
split torus. Let `R` be a Henselian local commutative ring, `k` a field with
a surjective algebra map `R → k`, and `G` a smooth affine group scheme over
`Spec R`. Suppose `H` is a supplied split torus with a homomorphism `s : H → G`.
Suppose also that `i₀ : T₀ → G_k` is a closed relative torus, and that a supplied
closed map `j₀ : H_k → T₀` satisfies the exact equality `j₀ ≫ i₀ = s_k`.
The construction returns an actual closed relative torus `T` over `Spec R`,
a closed inclusion `i : T → G`, an actual residue isomorphism `e : T_k ≅ T₀`
with `i_k = e.hom ≫ i₀`, and a closed map `l : H → T` with `l ≫ i = s`.
The data are stored in `ContainingLiftData`, which extends `LiftData`.
The result is uniform in universe `u` and in the characteristic. It has no
reductivity, connectedness or maximality premise.

The construction is internal. Its first input is the published
`HenselianTorusLifting.liftData` in `Torus.HenselianSubgroupLifting`, which
lifts `i₀` to a closed relative torus `L` with its exact residue square.
The closed inclusion into the affine `G` gives affineness of `L` by
`IsClosedSubgroup.isAffineHom`. The relative-torus smoothness theorem
`RelativeTorus.IsTorus.smooth_of_isLocalRing` gives smoothness of `L`.
`henselianClosedSplitHomLift` from `Torus.HenselianSplitSubgroupLifting`
then lifts `j₀ ≫ L.residueIso.inv` to a closed map from the given `H` into
`L`, retaining that residue map exactly. Its composite into `G` has the same
residue homomorphism as `s`.

The supporting theorem `exists_henselian_hom_conjugacy_of_residue_eq`
compares two maps out of the same split torus whose residue maps agree.
The identity point is a transporter between their residue maps, by
`PointwiseSchemeAction.isTransporter_of_comp_innerIso_eq` and
`innerIso_one_hom`. The published
`PointwiseSchemeAction.exists_henselian_transporter_of_split` lifts this
specified transporter to an integral section, still reducing to the
identity. The all-test transporter relation implies the exact conjugacy
equation by `IsTransporter.comp_innerIso_eq`. The proof uses no maximality
or source-isomorphism choice.

Conjugating the whole lifted torus inclusion by this section aligns the
lifted copy of `H` with `s`. Closedness is preserved by the ambient inner
isomorphism. The source torus and its residue isomorphism are unchanged.
`baseChange_innerIso_hom` identifies the residue of the inner automorphism
with the inner automorphism of its residue point; since that point is the
identity, the original exact residue inclusion is preserved. Classical
choice extracts `containingLiftData` from the implemented existence proof
`nonempty_containingLiftData`.

This module assembles existing exact lifting and transporter results and
asserts no new external source theorem. It does not choose a residue maximal
torus, construct an integral model of the initially supplied field torus,
or prove the fixed-pair special-apartment statement
`UnramifiedFixedPairSpecialApartmentStatement` that this module serves. Those are separate
uses of this containment construction.
