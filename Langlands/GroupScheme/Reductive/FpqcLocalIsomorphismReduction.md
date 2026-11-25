# Reduction of fpqc-local isomorphism to the affine split Isomorphism Theorem

`ReductiveFpqcLocalIsomorphismReductionStatement.{u}` is the proposition

```text
AffineSplitIsomorphismTheoremStatement.{u} →
  ReductiveFpqcLocalIsomorphismStatement.{u}.
```

`reductiveFpqcLocalIsomorphism_of_affineSplit` proves this implication for every
universe `u`. Both imported propositions retain their original definitions.
The affine split Isomorphism Theorem is an explicit hypothesis; this module
does not prove it or the unconditional fpqc-local isomorphism theorem.

This is an internal reduction between existing Library propositions, rather
than a new transcription of a source theorem. It makes explicit the root-datum
route described in the documentation of
[`FpqcLocalIsomorphismStatement`](FpqcLocalIsomorphismStatement.md), corresponding
to Conrad's Proposition 6.2.11(1). Its inputs are the published proof
`etaleLocalSplitReductive`, the published coordinate root-datum comparison, and
the transport results described below.

## Field fibres from a covering family

`exists_field_fiber_iso_of_cover` applies to any jointly surjective precoverage
`K`, an arbitrary `K`-cover of `S`, and two group schemes `G H` that become
isomorphic on every covering component. For every morphism `b : U → S` and every
point `x` of `U`, it supplies a field `k` in the scheme universe, a morphism
`c : Spec k → U` carrying the unique point to `x`, and an isomorphism between the
actual `c`-fibres of `G_U` and `H_U`. The cover's index universe can be different
from the scheme universe. There are no reductivity or flatness hypotheses.

The proof chooses a covering point `y` over `b(x)`, then a point `w` of
`U ×_S U_i` over both `x` and `y`, using the surjectivity of the map from the
scheme fibre product to the fibre product of its underlying sets. Take
`k = κ(w)` and the two projections of its residue-field point. Pull the given
isomorphism over `U_i` to `k`. The pullback square and `baseChangeCompIso`
identify its source and target with the required fibres.

## Comparing split groups on an affine base

`HasSplitMaximalTorusCoordinates.nonempty_iso_of_fieldIso` is conditional on
`AffineSplitIsomorphismTheoremStatement`. It takes two reductive groups over
`Spec R`, with supplied torus inclusions carrying
`HasSplitMaximalTorusCoordinates`, and any isomorphism of their actual fibres
over one field-valued point `Spec k → Spec R`. It concludes that the two groups
are isomorphic over `Spec R`.

Unpack the supplied coordinates to obtain the two closed coordinate maximal
tori, full fibrewise coordinate root data `P` and `Q`, and free actual root
lines. Interpret the field-valued point by its original coefficient map
`R → k`. Fibrewise maximality gives maximality of the two coordinate tori on
that field fibre, by
`splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`. The theorem
`IsFibrewiseRootDatumOf.nonempty_equiv_of_reductive_fieldIso` gives an equivalence
`P ≃ Q`, without assuming that the supplied field isomorphism respects the tori.
Its inverse has the direction required by the affine split theorem. Apply that
theorem with all the supplied data and retain its group isomorphism.

## Simultaneous splitting and cover assembly

`exists_etale_affine_iso_of_jointlySurjective_cover` has the same arbitrary
jointly surjective local-isomorphism cover hypothesis and assumes that both
groups are reductive and that the affine split theorem holds. It supplies an
affine étale neighbourhood of each point of `S` on which the groups become
isomorphic.

First use `etaleLocalSplitReductive` to split `G` on `Spec R → S` above the
chosen point. Apply it again to the pullback of `H` at the chosen point of
`Spec R`, obtaining `Spec A → Spec R`. The split data for `G_R` extend to
`A` by `HasSplitMaximalTorusCoordinates.baseChange_affine`. This published
transport preserves the same full coordinate root datum, fibrewise maximality,
and freeness of the actual root lines. The second splitting supplies the data
for `H_A`. The covering-family lemma gives a field-fibre isomorphism for the
direct pullbacks along `Spec A → S`; functorial composition isomorphisms
transfer it to the two successive pullbacks. The preceding conditional
comparison then gives an isomorphism over `Spec A`. Composition comparisons
transfer this back to the direct pullbacks from `S`.

Finally, `reductiveFpqcLocalIsomorphism_of_affineSplit` forgets the
quasi-compactness of the original fpqc cover, retaining its jointly surjective
flat cover. Choose the preceding affine étale neighbourhood for every point
of `S`. `Scheme.Cover.mkOfCovers` assembles them into an étale cover indexed by
the points of `S`, in universe `u`; the component isomorphisms give exactly the
conclusion of `ReductiveFpqcLocalIsomorphismStatement`. The construction also
handles the empty scheme, whose point-indexed family is empty. It requires no
compatibility of the component isomorphisms on overlaps, as none is requested
by the target.
