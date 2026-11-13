# Degrees of unitary generators

For a p-adic field `K`, the degree of a generator indexed by a unitary Weil or
supercuspidal representation is its positive rank, cast to the integers. The theorems
`LocalWeil.unitaryDegree_generator` and `PadicSupercuspidal.unitaryDegree_generator`
in `Langlands.VirtualRepresentation` unfold the unitary inclusion and ranked degree.

These two theorems are moved unchanged from `Correspondence/HenniartStableImage` to
share them with the Henniart composite-operation proof without a high-level import.
The field and representation universes remain independent.
