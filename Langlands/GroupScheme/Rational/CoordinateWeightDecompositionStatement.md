# Actual coordinate and augmentation weight decomposition: target

`CoordinateWeightDecompositionStatement` is an unproved proposition target,
not a theorem or a decomposition bundled as assumed data. It is the split-torus
weight decomposition used in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), §3.3, printed pp.107–108 / PDF pp.133–134, particularly
the passage from augmentation to its quotient in Example 3.3.2. The precise
all-algebra formulation is derived for the Library's coordinate choices.

For an arbitrary affine group over a field and an actual action of a split torus,
the proposition asks for the internal direct-sum decompositions of the actual
coordinate algebra, identity augmentation and augmentation cotangent. It also
asks that the image of each augmentation eigenspace under the actual quotient
map is exactly the cotangent eigenspace with the same character. Thus the target
includes lifting a cotangent eigenvector to an augmentation eigenfunction.

The action and its eigenconditions come from `CoordinateAction` and
`CoordinateCotangent` and quantify over every commutative coefficient algebra.
No finite-dimensionality or finite-support assumption is supplied as a premise:
internal direct-sum decomposition is the conclusion. No characteristic restriction,
smoothness or connectedness is imposed. The proof remains an explicit successor
obligation; this statement assumes neither semigroup realization nor the
commutator bound. This target concerns coordinate and cotangent decomposition,
not the separate intrinsic Lie decomposition being developed with tangent images.
