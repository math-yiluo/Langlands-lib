# The ambient hyperbolic-plane isometry morphism

Authors: Worker 124.

Let `K` be a field, `D` a finite-dimensional division `K`-algebra, `σ` a
first-kind involution, and `q` a quaternionic quadratic form on `D^n`, where
`n` is any finite index type in `Type`. Given an actual hyperbolic pair `e,f`,
this module constructs a homomorphism

`HyperbolicScheme.isometryHom h : O(H) → O(q)`

from the isometry group of the binary hyperbolic form. Its action extends the
binary isometry by the identity on the polar orthogonal complement. No
quaternion-dimension, centrality, local-field, nondegeneracy, infinitude or
characteristic assumption is required for this construction.

Write `E` for `planeInclusion e f` and `R` for the actual polar-coordinate
`planeRetraction σ q e f`. Their identity `E R = 1` persists over every
commutative `K`-algebra `C`. On binary matrix units over `C ⊗[K] D`,
`extendUnits h C` is the actual unit with matrix

`U = R_C M E_C + (1 - R_C E_C)`.

Its inverse is obtained by applying the same multiplicative construction to
`M⁻¹`. The published `SplitMatrixExtension.recover` identity recovers `M`,
so `extendUnits_injective` holds over arbitrary coefficient algebras, including
those with nilpotents. Entrywise coefficient extension and
`SplitMatrixExtension.value_map` prove naturality under every coefficient map.

For a relative test scheme `T`, `matrixPointsEquiv` uses the actual global
sections algebra `C = Γ(T)` and `TensorMatrix.equiv` to identify points of the
represented matrix-unit group with these matrix units. The resulting natural
family of point homomorphisms defines the actual group-scheme morphism
`unitHom h` by `homOfPoints`. Its point formula and injectivity hold on all
relative test schemes, without an affineness restriction on `T`.

The factorization into `O(q)` uses the actual quotient form, rather than only
its polar form. The published adapted representative of `q` is

`Q' = R H R* + P Q P*`, where `P = 1 - R E` and `Q = Quotient.out q`.

`scalarMatrix_splitRepresentative` identifies its coefficient extension with
this same expression over `C`. `SplitQuadraticExtension.defect_mem` proves
that an alternating binary defect gives an alternating ambient defect. The
`TensorMatrix` adjoint and alternating-subspace comparison then translate
this calculation into the defining range condition for the actual closed
inclusion `isometryGroupι q`. Its representing property supplies
`isometryHom h`, and `isometryHom_comp` identifies the composite with the
prescribed matrix-unit morphism. `isometryHom_points` gives its matrix formula
on every relative test; `isometryHom_points_injective` proves that it loses
no binary isometry point.

This is an internal derivation from the published split-matrix extension,
adapted representative, tensor-matrix comparison and represented isometry
cut. It asserts no lifting to an arbitrary spin cover, no comparison with the
entire spin kernel, and no elementary-generation or Kneser–Tits conclusion.
Those remain subsequent obligations of the host proof task.
