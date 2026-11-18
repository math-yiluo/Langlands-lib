# The full minimal chamber and its common-uniformizer section

This internal actual-point transport describes the full chamber as a
compact thickening of its published lattice section.

`rationalMinimalTorusCompactKernel i` is the image in the ambient group of
the torus's intrinsic common rational-character norm kernel. Its points
belong to the ambient common norm kernel by functoriality of character
restriction. If the torus is split, the subgroup is compact in the
canonical rational-point topology, using the published compactness of
the split-torus norm kernel and continuity of the point map.

The theorem `rationalMinimalChamber_eq_compactKernel_mul_section` proves
the set equality

```text
full minimal chamber =
  mapped torus norm kernel * common-uniformizer minimal chamber section.
```

The uniformizer-section theorem supplies a representative `s` for every
torus point `x`, with `x s⁻¹` in the torus norm kernel. Character orders
vanish on that kernel, so `s` has the same orders as `x` and lies in the
section chamber whenever `x` lies in the full chamber. Mapping
`x = (x s⁻¹) s` to the ambient group gives one inclusion. For the reverse
inclusion, multiply a section point by a norm-kernel point; all its
simple-root orders remain unchanged.

`rationalMinimalChamberInNormKernel_eq_compactKernel_mul_section` proves
the corresponding equality after intersecting the full chamber and
section with the ambient actual common norm kernel. The same compact
factor works because it is already contained in that ambient kernel.

The split torus need not be maximal for these identities; no Xi,
constant-term, Cartan-cover or decay estimate is assumed. The result
preserves the distinction between the full ambient chamber and the
lattice section. It includes the empty simple-root case.
