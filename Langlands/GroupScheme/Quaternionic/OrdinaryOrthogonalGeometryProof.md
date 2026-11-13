# Proof: smoothness and absolute almost simplicity of even orthogonal groups

This module proves the published statement
`Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement` at an arbitrary
universe `u`, as the theorem `Langlands.GroupScheme.Quaternionic.ordinaryOrthogonalGeometry`.

Let `K` be any field, of any characteristic (characteristic `2` included), and let
`m ≥ 3`. Let `q` be a quadratic form of rank `2m` for the scalar involution
`FirstKindInvolution.scalar K` that is nondegenerate in the published sense
`IsNondegenerateQuadratic`, that is, its polar matrix `Q + ᵗQ` is invertible. The theorem
says that the orthogonal group scheme `O(q) = (scalar K).isometryGroup q` is smooth and that
its identity component `(scalar K).connectedIsometryGroup q` is absolutely almost simple.

## Route of the Lean proof

1. **Matrix representative.** `q` is the class of some matrix `Q : Matrix (Fin (2m)) (Fin (2m)) K`
   (`Submodule.Quotient.mk_surjective`). By the published
   `FirstKindInvolution.isNondegenerateQuadratic_scalar_mk_iff`, nondegeneracy means that
   `Q + ᵗQ` is a unit.
2. **Splitting over an algebraic closure.** Let `L = AlgebraicClosure K`.
   `OrthogonalMatrix.nonempty_splittingIso` (module `OrthogonalMatrix.Comparison`) gives an
   isomorphism of group schemes over `Spec L` from the base change of `O(q)` to the split
   orthogonal group `OrthogonalMatrix.groupScheme (Fin m) L` of the hyperbolic form
   `Σ x_a y_a` (module `OrthogonalMatrix.Basic`). It rests on a hyperbolic basis over the
   algebraically closed field `L`, which holds in every characteristic (module
   `OrthogonalMatrix.Hyperbolic`).
3. **The split group.** The split orthogonal group is smooth and affine over its base
   (modules `OrthogonalMatrix.Smooth`, `OrthogonalMatrix.Subgroups`). The auxiliary theorem
   `OrthogonalMatrix.isAbsolutelyAlmostSimple_identityComponent l hl K` of this module
   proves that, for `l` with at least three elements and every field `K`, its identity
   component is absolutely almost simple:
   - over each algebraically closed field `k` the identity component is semisimple
     (`isSemisimple_identityComponent`) and nontrivial (`range_id_identityComponent_ne_bot`),
     both from module `OrthogonalMatrix.Semisimple`, which needs only that `l` has at least
     two elements (obtained from `3 ≤ card l` by `Fintype.one_lt_card_iff_nontrivial`);
   - given these, it is almost simple by `isAlmostSimple_identityComponent` (module
     `OrthogonalMatrix.TypeD`, the type `D_l` root system argument, which uses
     `3 ≤ card l`);
   - `isAbsolutelyAlmostSimple_of_isAlmostSimple` (module `OrthogonalMatrix.Semisimple`)
     turns almost simplicity over all algebraically closed fields into absolute almost
     simplicity over every field.
   With `l = Fin m` and `3 ≤ m` this applies over `L`.
4. **Descent.** The published
   `IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso` takes the
   isomorphism of step 2 with a smooth affine group whose identity component is absolutely
   almost simple. It returns smoothness of `O(q)` and absolute almost simplicity of its
   identity component over `K`, which is the statement.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. It
does not use `LocalSpinRankOneStatement`, `LocalKneserTitsStatement` or any other statement
whose planned proof consumes this one.

## Helper modules

The proof depends on the following new internal modules, each with its own Markdown:
`Langlands.GroupScheme.OrthogonalMatrix.Basic`, `.Smooth`, `.Subgroups`, `.LieAlgebra`,
`.Torus`, `.Roots`, `.Reductive`, `.Semisimple` (the split orthogonal group, its smoothness,
diagonal torus, roots, reductivity and semisimplicity), and `.Hyperbolic`, `.Comparison`,
`.TypeD` (the hyperbolic basis, the splitting isomorphism and the type `D` almost
simplicity argument).
