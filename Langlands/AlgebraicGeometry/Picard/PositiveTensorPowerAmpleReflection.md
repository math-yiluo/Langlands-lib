# Ampleness reflected by a positive actual tensor power

For actual line bundles `L,M` on an arbitrary scheme and `n > 0`,
`LineBundle.IsAmple.of_positive_tensorPower_iso` proves that an
isomorphism `M.obj ≅ tensorPow L.obj n` and ampleness of `M` imply
ampleness of `L`, in the existing section-generation-locus sense.

Take a point and a section of a positive tensor power `M^k` whose
generation open contains the point and is affine. The given sheaf
isomorphism and the actual iterated-tensor-power comparison give an
isomorphism `M^k ≅ L^(n*k)`. Transporting the section preserves its
whole generation open. Since `n*k` is positive, this section witnesses
the required local ampleness condition for `L`; compactness comes from
the supplied ampleness of `M`.

The provenance is internal: the proof directly uses the existing
ampleness predicate, the actual tensor-power isomorphisms and invariance
of section generation opens under a module-sheaf isomorphism. No
noetherian or geometric regularity hypothesis is added.
