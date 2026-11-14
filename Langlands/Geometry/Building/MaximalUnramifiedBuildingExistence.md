# Actual unramified building data on a prescribed maximal split torus

For a nonarchimedean local field `F : Type u`, a connected reductive affine
group `H` over the actual field `inertiaFixedField F`, and a prescribed maximal
split torus `i : S.toGrp ⟶ H`,
`MaximalUnramified.prescribedBuildingData F hH i hi` constructs
`MaximalUnramified.BuildingData F H`. Its torus is definitionally `S` and its
inclusion is definitionally `i`, as recorded by the two projection lemmas.
It supplies a normalizer-stable equipollence class of root-datum valuations,
an actual centralizer datum, and full integer-valuation centralizer
compatibility on that same class.

The construction composes published Library results. The theorem
`MaximalUnramified.isQuasiSplit` applies
`unramifiedQuasiSplit_of_henselianDiscrete` to the proved generic theorem
`henselianDiscreteQuasiSplit`. The published maximal-unramified valuation is
surjective and has a henselian valuation ring. Applying the proved
`quasiSplitIntegerApartmentExistence` to this valuation and the prescribed
torus gives an apartment datum and a compatible centralizer datum. Classical
choice selects both, and the structure retains the supplied torus, inclusion,
maximality proof and connected reductivity proof.

This is an internal composition of those constructions, with arbitrary
universe `u` and no restriction on field or residue characteristic. The
construction requires a prescribed maximal split torus and does not choose
one. It does not assert a Galois action, Galois stability, a descent comparison,
or chamber transitivity. These remain separate inputs when the construction
is used for the local anisotropic affine-diagram theorem.
