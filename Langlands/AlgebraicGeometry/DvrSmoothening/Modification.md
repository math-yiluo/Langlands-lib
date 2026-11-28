# Morphisms which are isomorphisms over an open, and resolved points

- `isIso_morphismRestrict_of_le`, `isIso_morphismRestrict_comp`: being an isomorphism over an open
  passes to smaller opens and to composites.
- `exists_lift_of_isIso`: a morphism into the open over which `g` is an isomorphism lifts along `g`.
- `smoothLocus_congr`: equal morphisms have equal smooth loci.
- `GenericallySmooth f`: every point of `X` over the generic point of `Spec R` lies in the smooth
  locus of `f`. `GenericallySmooth.comp`: preserved by a morphism which is an isomorphism over an
  open containing the generic fibre.
- `Resolved g P`: the test point `P` lifts along `g` with closed point in the smooth locus of the
  composite. `Resolved.comp`: preserved by a further morphism which is an isomorphism over an open
  containing the smooth locus.

Internal notions for the induction of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.4.
