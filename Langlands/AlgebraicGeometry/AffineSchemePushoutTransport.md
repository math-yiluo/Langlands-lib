# Transporting the canonical affine pushout

Let `A`, `B`, `C`, and `D` be arbitrary objects of `CommRingCat` in
universe `u`, with displayed maps `i : A ⟶ B`, `j : A ⟶ C`,
`f : B ⟶ D`, and `g : C ⟶ D`. Assume that `h : IsPullback i j f g`.
Write `P = RingHom.pullback f.hom g.hom`, the compatible-pair subring
of `B × C`.

## Comparison with the canonical cone

`canonicalPullbackIso h` is the isomorphism
`A ≅ CommRingCat.of P` supplied by uniqueness of limits. The two limiting
cones are the one obtained from `h` and Mathlib's
`CommRingCat.pullbackCone f g`, whose point and projections are
definitionally the compatible-pair subring and its projections.
The lemmas `canonicalPullbackIso_hom_fst` and
`canonicalPullbackIso_hom_snd` prove that the isomorphism's homomorphism
followed by the canonical first or second projection equals `i` or `j`,
respectively. They use the corresponding factorization equations for
the limit comparison isomorphism. No surjectivity or nontriviality
hypothesis is required for this comparison.

## Pushout transport

For any category `E` and any functor `F : CommRingCatᵒᵖ ⥤ E`,
`isPushout_map_of_canonical F h hc` takes as its additional input a
pushout square `hc` whose maps are the actual images under `F` of
`f`, `g` and the two canonical projections, with arrows reversed.
It concludes that the images of the displayed maps `f`, `g`, `i`, and
`j` also form a pushout square.

The proof applies `IsPushout.of_iso` with identity isomorphisms at
`F(D)`, `F(B)`, and `F(C)`, and with the image under `F` of the
opposite of `canonicalPullbackIso h` at the cocone point.
Functoriality and the two comparison equations verify the required
commuting squares. This uses no preservation-of-colimits assumption:
the old and new cocones are isomorphic over the same diagram.
The category `E` may have its own object and morphism universes.

`isPushout_specMap_of_canonical` specializes this transport to
`Scheme.Spec`, giving the desired arbitrary displayed square in all
schemes once the canonical scheme pushout has been proved.
`isPushout_specTopMap_of_canonical` specializes it to `Spec.toTop`,
with actual continuous spectrum maps in `TopCat`.
Both helpers retain the canonical pushout as an explicit premise;
this module does not prove that premise or the final affine scheme
pushout statement. No affine-target restriction is imposed by the
scheme specialization.

## Provenance

These are derived internal adapters for the assigned affine scheme
pushout proof. They apply Mathlib's limit comparison and invariance
of pushouts under isomorphism to the canonical compatible-pair ring.
They do not assert an additional external mathematical result and
do not alter the published statement or any of its imports.
