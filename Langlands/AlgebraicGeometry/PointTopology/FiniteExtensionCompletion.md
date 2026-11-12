# Completing finite extensions of normed fields

Author: Worker 157.

This internal prerequisite supplies the finite-extension step in the completion
reduction used on printed p.19 of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad observes that the degree of the completed extension is at most the original
finite degree. The module proves finiteness, which is the consequence needed by
the rational-point embedding argument; it does not assert the degree bound.

For nontrivially normed fields `K` and `L` with `NormedAlgebra K L`, the namespace
`FiniteExtensionCompletion` constructs the isometric map between the completions
by extending `algebraMap K L`. Its `algebra` and `normedAlgebra` definitions give
the canonical normed algebra structure on the completed extension. They are
explicit definitions, used as local instances in this module. The scalar-tower
instance records compatibility with the original `K`-algebra structure.

The map `tensorMap` sends `K̂ ⊗_K L` to `L̂`, multiplying the completed base-field
embedding and the original inclusion of `L`. If `L/K` is finite, its image is a
finite-dimensional subspace over the complete nontrivially normed field `K̂`.
Mathlib's closedness theorem for finite-dimensional subspaces makes this image
closed. It contains the dense image of `L`, so it is all of `L̂`.
`tensorMap_surjective` proves this, and `finiteDimensional` transfers finite
dimensionality along the surjection.

The proof is derived from the universal property of completion, tensor-product
base change for finite modules, and closedness of finite-dimensional subspaces.
The source motivates the required conclusion; the implemented proof uses the
tensor-product image argument. Neither henselianity, separability, completeness
of the original fields nor `IsModuleTopology K L` is assumed. The fields may lie
in different universes.
