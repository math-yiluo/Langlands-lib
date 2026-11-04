# Actual ambient and Levi cokernel bridges on full smooth subcategories

Worker 1300. Internal constructions for assembling the associated-Levi
comparison. These are natural cokernel presentations of its two sides;
they do not identify the two different cokernels.

`StandardComplex.jacquetSharpCokernelIsoOn` precomposes the inverse of
`StandardComplex.jacquetSharpCokernelIso` with `C.ι`, for any object property
on the full smooth category at the published closed carrier universe. Its
source is literally `C.ι ⋙ StandardComplex.sharpFunctor I ⋙ jacquetFunctor I`.
The target is the actual cokernel of the Jacquet image of the incoming
signed differential, restricted to `C`. The compact-limit premise needed
for Jacquet exactness remains explicit. Taking `C` to be the published
`TerminalJacquet.supportObjects I` gives exactly the ambient functor form
needed by the associated-Levi target.

`conjugationFunctor_mapsShortExactIntertwiners` uses the definition of
`conjugationFunctor`: pullback retains every underlying linear map. Its
exactness therefore holds for every actual short exact sequence on all
smooth objects. The supplied membership equivalence is precisely
`x ∈ N ↔ g⁻¹ * x * g ∈ M J`, and the actual representation action remains
`σ(g⁻¹ * x * g)`. No normalizer or conjugation law is manufactured.

`LeviComplex.incomingDifferentialNat` and `sharpProjectionNat` use the
published `family` of subgroups inside `M J`, the same local compactness
instance provided by closedness of `M J`, and exactly the definition of
`LeviComplex.sharpFunctor`. Applying
`StandardComplex.sharpCokernelIso` to actual conjugation yields
`conjugationSharpCokernelIso`. The projection theorem is an equality of
natural transformations with the original conjugated quotient projection.

`LeviComplex.jacquetConjugationSharpCokernelIsoOn` takes the inverse and
precomposes with `C.ι` and actual normalized Jacquet at `J`. Its source is
literally
`C.ι ⋙ jacquetFunctor J ⋙ LeviComplex.sharpFunctor J Finset.univ ⋙ conjugationFunctor g`.
The target is the corresponding actual conjugated incoming-differential
cokernel with the same precomposition. It requires no Jacquet exactness
premise: here Jacquet is only a precomposition. The full-support Levi
quotient has degree zero, already covered by the zero incoming map, so no
positive-rank hypothesis is introduced.

All constructions retain independent root, group, and carrier universes and
all actual equivariant maps in the full subcategory. No support membership
deduction, Bruhat filtration, surviving-cell identification, graded exactness,
or comparison between the ambient and Levi cokernels is proved or assumed.
The provenance is elementary natural-isomorphism precomposition and
specialization of the paired terminal/Jacquet cokernel modules. Their named
representation-theoretic input is full-smooth Jacquet exactness under the
displayed compact-limit hypothesis; no Langlands-classification,
character-independence, geometric-lemma, adjointness, or Aubert Proposition
3.2 assertion is invoked by these bodies.
