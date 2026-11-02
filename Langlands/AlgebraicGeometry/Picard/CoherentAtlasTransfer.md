# Actual coherent-family to Picard atlas transfer

For arbitrary schemes `X S : Scheme.{u}` and a flat morphism `f : X ⟶ S`,
`PicardGroupoid.toFamilyHomLiftStrongTrans f` is the actual inclusion from
`PicardGroupoid.relativeHomLift f` to
`homLift.{u + 1} (CoherentSheaves.FamilyGroupoid.pseudofunctor f)`.
It applies the generic `homLiftStrongTrans` construction to the actual
`toFamilyStrongTrans f`. This preserves its identity and composition
coherence and its naturality on the full scheme slice.

The component object is definitionally the explicit hom lift of
`relativeToFamily f T` applied to the original line bundle. The lemma
`toFamilyHomLiftStrongTrans_obj` records this exact formula.
`toFamilyHomLiftStrongTransFullyFaithful` lifts the supplied inverse on
each Hom set from `toFamilyStrongTransFullyFaithful`; no essential
surjectivity is assumed.

If `f` is also universally closed and locally of finite presentation,
`hasLocallyFiniteTypeSmoothSchemeAtlas_of_familyAtlas` transfers any actual
coherent-family scheme atlas locally of finite type over `S` to the
original concrete Picard atlas predicate. Its proof supplies the actual
lifted transformation, its full faithfulness and its object formula to
`hasLocallyFiniteTypeSmoothSchemeAtlas_of_coherentAtlas`. That construction
uses the actual atlas family's rank-one open, its line bundle, and
factorization of all ambient points against line bundles through that
open. It transports the entire presheaf on the full slice using the same
representing scheme and smooth surjective structure morphism. The open
atlas remains locally of finite type over `S`. The transformation is
constructed here, rather than retained as an additional hypothesis.

`fieldPicardStackAtlas_of_coherentStackAtlas` then proves the implication
from `CoherentSheaves.FieldCoherentStackAtlasStatement.{u}` to the exact
`FieldPicardStackAtlasStatement.{u}`. For every field `k : Type u` and
proper scheme `X` over `Spec k`, Mathlib's field-base and noetherian-base
instances give flatness and local finite presentation of `X.hom`;
properness gives universal closedness. The preceding transfer applies to
the coherent atlas supplied by the hypothesis. The argument retains
arbitrary fields, arbitrary proper schemes and every slice test scheme.

The provenance is internal composition of the actual family comparison,
explicit hom lift, rank-one atlas restriction, and Mathlib's geometric
instances. Worker 152 authored the reused actual comparison;
its private core-pseudofunctor helper adapts Worker 214's published family
pullback construction. This module proves the conditional atlas transfer
and the implication of the two field statements. It supplies no
unconditional coherent-atlas existence proof, so the final Picard field
statement still requires that separate input.
