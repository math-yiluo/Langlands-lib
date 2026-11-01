# Right and left exterior insertion on cut diagrams

This internal algebraic comparison uses the existing actual cut diagram and
all of its unchanged inclusion maps. The index and coefficient universes are
independent, and no dimension or finite-length assumption is imposed on the
complex coefficient modules.

The existing `position s i` counts target cuts smaller than the inserted cut
`i`, so its `sign s i` is the sign for inserting on the left and sorting the
increasing basis. `rightPosition s i` instead counts target cuts larger than
`i`. Thus `rightSign s i` is the sign for appending on the right and sorting
increasingly. If `i ∈ s`, these two positions partition `s.erase i`.
Consequently, when `s.card = k + 1`,

```text
rightSign s i = (-1)^k * sign s i.
```

`rightStep` applies exactly the same diagram inclusion as `step` and uses the
right insertion sign. Extension of a homogeneous family of degree `k` is zero
outside that degree. The preceding sign identity therefore proves
`rightStep_extend` on every coordinate, including the zero coordinates.
Summing over the finite cut index set and restricting to degree `k + 1`
gives the identity of actual linear maps

```text
rightDegreeDifferential k = (-1)^k • degreeDifferential k.
```

The scalar `degreeOrientation k` is `(-1)^(k.choose 2)`. Its exponent equals
`k * (k - 1) / 2`, and Pascal's identity gives
`degreeOrientation (k + 1) = (-1)^k * degreeOrientation k`. Each scalar squares
to one. Hence multiplication by it defines the involutive linear equivalence
`degreeOrientationEquiv k` on the actual homogeneous carrier.
`degreeOrientationEquiv_commutes` proves that these equivalences carry the
existing left insertion differential to the right insertion differential.
This is an explicit degreewise isomorphism of complexes; the differentials
are actual maps, not only classes or Euler characteristics.

The homogeneous right differentials square to zero. Multiplying a linear map
by a nonzero scalar preserves its kernel and range, so the module also proves
equality of the actual kernels and images for the two conventions, equivalence
of injectivity, and equivalence of middle exactness.

The provenance is internal: a finite-set partition, the existing cut diagram
definitions, elementary powers of minus one, Pascal's identity, and basic
linear algebra prove all claims. This module does not construct a Bruhat
filtration, identify an actual geometric graded piece, compare orbit
integrals, or prove concentration or signed Aubert effectivity. Those
applications must still identify their actual graded transition maps with
the chosen insertion convention.
