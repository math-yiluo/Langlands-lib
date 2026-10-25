# Surjectivity of idele-class norms for almost-everywhere split extensions

Author: Worker 50. Coauthors: Worker 226 and Worker 269, who coordinated the
analytic inputs and their interface with this assembly proof.

`Langlands.Global.AdelicFunctoriality.almostEverywhereSplitIdeleClassNormSurjective.{u,v}`
proves exactly the published proposition
`AlmostEverywhereSplitIdeleClassNormSurjective.{u,v}` from
[AlmostEverywhereSplitNormStatement](AlmostEverywhereSplitNormStatement.md).
The number fields have independent universes. For a Galois extension `E/F`
with cyclic automorphism group, if every finite completed extension above a
prime outside a finite set `S` has degree one, the actual
`ideleClassNorm (K := F) (L := E)` is surjective.

The only extra arithmetic hypothesis is the splitting condition already in
the target. In particular, approximation and local norm neighborhoods are
proved imported results, not additional premises. The target statement and
its imports are unchanged. The intermediate assembly lemmas do not require
Galoisness or cyclicity; the final theorem retains the exact published type.

## Local lifts and restrictedness

`localNorm_units_completionMap_of_finrank_eq_one` proves that scalar inclusion
on local units is a right inverse to the norm when the completed degree is
one. Apply `Units.ext` and the published norm-of-scalar formula
`FiniteExtension.localNorm_algebraMap`, then simplify the exponent one.

`completionMap_unit_integral` proves that scalar inclusion preserves integrality
of a local unit and of its inverse. Both assertions follow from
`FiniteExtension.completionMap_mem_integers_iff`.

`mem_range_ideleNorm_of_split_and_local` takes one selected finite place and
one selected infinite place above each base place. Assume local norm preimages
at the finite places in `S` and at every infinite place. Choose these preimages
at those places. At finite places outside `S`, use scalar inclusion of the
base coordinate, whose norm is that coordinate by completed degree one.

The base idele and its inverse are integral at almost every finite place.
Intersect these two cofinite sets with the complement of `S`. On this cofinite
intersection, both the chosen upper unit and its inverse are integral by the
preceding helper. The published `mem_range_ideleNorm_of_local` from
[IdeleNormLift](IdeleNormLift.md) then assembles an upper idele, using the chosen
preimage at one upper place and `1` at the others, and identifies its norm
with the original base idele. This accounts for restrictedness of both the
idele and its inverse, and for every archimedean factor.

## Principal adjustment and the quotient

`surjective_ideleClassNorm_of_principal_adjustment` assumes every base idele `a`
has a principal adjustment `(unitEmbedding α)⁻¹ * a` in the range of the actual
idele norm. Choose an upper idele with this norm. The formula
`ideleClassNorm_mk` computes its class norm. The principal idele has trivial
class by `QuotientGroup.eq_one_iff`, so the result is the class of `a`.
Quotient induction gives surjectivity on all idele classes.

`exists_infinitePlace_above` uses `InfinitePlace.comap_surjective` to select an
upper infinite place. `surjective_ideleClassNorm_of_split_and_adjustment`
combines the local lifting lemma with the quotient argument. Its explicit
adjustment hypothesis is discharged in the final theorem as follows.

For the fields `F`, `E` and finite set `S` in the exact target, select each
upper finite place using `placeAbove E` and each upper infinite place using
`exists_infinitePlace_above`. Specialize the splitting hypothesis to these
selected finite places and their lying-over witnesses. The witnesses install
the same canonical completion algebra as in the target.

For any base idele `a`, apply `exists_principal_inv_mul_mem` from
[MixedWeakApproximation](MixedWeakApproximation.md), taking the prescribed
sets to be the images of the local unit norms. The neighborhood hypotheses
are exactly `range_finiteLocalNorm_mem_nhds` and
`range_infiniteLocalNorm_mem_nhds` from
[LocalNormNeighborhood](LocalNormNeighborhood.md). This simultaneously
produces one nonzero principal multiplier at the exceptional finite places
and at all infinite places. The conditional assembly lemma now gives the
required surjectivity. No splitting assumption at infinite places is used;
in particular the argument needs only a norm neighborhood at real places,
not surjectivity of every archimedean local norm.

## Provenance

This is the intermediate norm-surjectivity argument in Artin and Tate,
*Class Field Theory* (2009), Chapter V §4, proof of Theorem 2, printed page 17
(PDF page 26). The registered source is `artin-tate-2009-class-field-theory`,
SHA-256 `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata on PDF page 202 do not correct this passage.

The Lean proof implements the local-lift, principal-adjustment and quotient
steps described above. Its imported mixed approximation theorem uses weak
approximation for actual absolute values; its imported norm-neighborhood
theorems use the inverse function theorem for powers and the norm-of-scalar
formula. The argument stops at surjectivity. It does not invoke a global
norm inequality or infer that the global extension is trivial.
