# Generic maximality from a residue-maximal split torus and a reference

This internal construction transfers generic maximality between actual integral
split tori in a supplied model. It works over a commutative domain `R` with
fraction field `K`, with `M : IntegralModel R K G`. All types have arbitrary
common universe `u` and either characteristic is allowed.

For two commutative group schemes `T,T'` over `R` and integral maps
`i : T.toGrp → M.group`, `i' : T'.toGrp → M.group`, an actual
`A : SplitTorusConjugator i i'` gives an isomorphism of their generic source
tori and the square

    M.genericHom i ≫ Int(A.genericPoint M) =
      groupHom(A.torusIso_K.hom) ≫ M.genericHom i'.

`SplitTorusConjugator.isMaximalSplitTorus_generic_iff` proves maximal split
torus structure for the left generic map is equivalent to that for the right
generic map. It reads the actual commutative source isomorphism as an
isomorphism of group schemes, packages this square as `SubgroupConjugate`,
and applies the published `SubgroupConjugate.isMaximalSplitTorus_iff` in
`Torus.UnipotentQuotientMaximalSplit`. This lemma itself does not assume
Henselianity, smoothness, connectedness or reductivity.

`M.henselianSplitTorusConjugatorOfResidueGeneric` assumes `R` is Henselian
local, `M.IsSmooth`, a surjective algebra map `R → k` to a field, connectedness
of the actual `k`-fibre of `M.group`, and connected reductivity of the
specified generic group `G`. Both integral source tori are split. The
reference map `i'` is closed and `M.genericHom i'` is a maximal split torus.
For the target map `i`, maximal split torus structure is assumed only in the
actual `k`-fibre. No generic maximality premise is imposed on `i`.

The constructor transports the reference generic maximality and connected
reductivity through `M.genericIso`, uses the published
`isMaximalSplitTorus_residue_of_generic` to prove reference residue
maximality, then invokes `henselianSplitTorusConjugatorOfResidue`.
The latter constructs an actual integral section and integral source
isomorphism from residue conjugacy, extension of the residue source
isomorphism, and a smooth Henselian transporter lift.

Finally `M.isMaximalSplitTorus_generic_of_residue_of_reference` constructs
that same conjugator and applies its generic maximality equivalence to the
reference generic maximality. It proves the target generic map is a maximal
split torus, including its closedness. An integral closedness hypothesis for
the target map is unnecessary because the actual integral conjugator already
identifies it with the closed reference.

The provenance is derived model and conjugacy glue. The inputs are
`IntegralModel.SplitTorusConjugacy`, `Torus.HenselianSplitRank` and
`Torus.UnipotentQuotientMaximalSplit`. The integral model need not be
reductive. The existence of a closed generically maximal integral reference
torus remains an explicit hypothesis; this module asserts no unrestricted
converse to rank specialization. It constructs no model, residue-maximal
torus, splitting of a nonsplit integral torus, or apartment.
