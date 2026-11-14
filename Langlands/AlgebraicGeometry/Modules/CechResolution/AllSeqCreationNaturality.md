# Naturality and refinement of positive-degree creation

This internal module extends the existing degree-one cup naturality and cover
refinement formulas to creation on every positive degree. It is derived from
the actual ordered Čech cup, pullback, refinement and resolution comparison
maps in the Library. Worker 327 authors this extension; the comparison and
pullback infrastructure is from Worker 5218.

For any morphism of schemes and any map of covering indices subordinate to its
inverse images, `Cech.pull_cup₁_all` proves that pullback of `cup₁ z b` equals
`cup₁ (pull z) (pull b)` for a one-cochain `z` and a cochain `b` of any degree
`q`. The proof evaluates on a tuple, uses multiplicativity of the morphism on
sections and the existing `face_pull` formula. `Cech.refine_cup₁_all` proves
the corresponding identity for cover refinement by the multiplicativity of
restriction and `face_refine`. Neither identity requires cocycles, affine opens
or a covering condition.

`AllSeq.unitCochainMap_cup_all` and `AllSeq.refineCochain_cup_all` express these
identities for the scalar-linear ordered complexes of the structure sheaf over
a commutative ring `R`. Here the cover index types are finite and in the same
universe as the schemes. The scalar actions are those of the structure maps.

`homologyMap_creationH` states that the ordered pullback commutes with
`creationH` from degree `n+1` to degree `n+2`, for every natural number `n`.
Surjectivity of the cocycle class maps reduces it to the cochain identity.
The proof uses the representative formula for creation and naturality of the
homology class map; equality of cocycles follows from equality of their cochains.

`unitCohomologyPullback h n` names the composite of the canonical relative
cohomology pullback with the pullback-unit comparison in degree `n`. It is a
morphism of `R`-modules and has no cover, separatedness or affine hypothesis.

For separated structure maps and finite affine families covering the source
and target schemes, `pull_creationCanonical` transports this identity to actual
structure-sheaf cohomology. The pullback is the canonical
`relativeCohomologyPullback` followed by the pullback-unit comparison. Thus it
commutes with creation by an actual `H¹` class on every `Hⁿ⁺¹`. The proof
uses the existing compatibility of the ordered resolution equivalence with the
actual pullback.

Under the same separated and finite affine cover conditions,
`creationCanonical_refine` proves equality of creation on a cover and its
refinement on every `Hⁿ⁺¹`. It uses cocycle representatives, the existing
`canonicalClass_refine` identity, and the new cochain refinement identity.

The canonical conclusions here concern positive input degrees. No contraction
relation, exterior generation, or geometric dimension theorem is asserted.
The module uses no characteristic hypothesis and no additional external source.

The `ModuleCat` morphism `unitCohomologyPullback` has underlying linear map
`unitCohomologyPullbackLinear`, defined in
[AllSeqMixedSlant](AllSeqMixedSlant.md). The two interfaces retain their respective types.
