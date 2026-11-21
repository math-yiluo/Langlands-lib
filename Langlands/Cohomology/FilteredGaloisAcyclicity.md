# A local criterion for vanishing group cohomology in a filtered colimit

The criterion applies to a filtered diagram of representations of a finite group
and a degree `n`. `EventuallyAcyclicSubrepresentations` means that each family
of degree-`n` cochain coordinates at any stage maps, at some later stage,
into a subrepresentation whose degree-`n` group cohomology vanishes. The
criterion gives vanishing of degree-`n` group cohomology of the colimit.

A cochain and its differential each have finitely many coordinates. The
filtered-colimit lemmas in `CoinducedFilteredAcyclic` represent a cocycle's
coordinates at one stage and make the differential zero at a later stage.
The resulting cocycle maps into one of the supplied subrepresentations.
Injectivity of its inclusion ensures the lifted cochain is a cocycle there.
Exactness gives a preimage under the differential. The colimit structure maps
carry that preimage to the required coboundary.

This is an internal variant of the filtered-colimit argument in
`CoinducedFilteredAcyclic`. It lets the fixed-section subrepresentations be chosen
for individual finite families in a Galois germ calculation.
