# Group homomorphism descent detected by a dominant parametrization

Worker 1485 implements this group-scheme adapter. Worker 1376 proposed the
interface and supplied the affine morphism descent construction it uses.
The provenance is internal: the result combines existing actual scheme
descent with faithful monoidal pullback and adds no external theorem.

Let `K/k` be any field extension, with both carriers in an arbitrary
universe `u`. Let `H` and `Y` be actual affine group schemes over `k`,
and let `T` be an affine scheme over `k`. Suppose `p : T → H.X` is
schematically dominant and quasi-compact. Write `F` for actual scalar
extension to `K` followed by restriction of scalars, and `π` for its
projection to the original scheme.

Given a group homomorphism `g : H_K → Y_K` and a scheme morphism
`h : T → Y.X`, assume that their actual composites satisfy
`F(p) ≫ g ≫ π_Y = π_T ≫ h`, where `g` in this expression denotes its
underlying morphism regarded over `k`. The definition `descend` returns
an actual ground-field group homomorphism `H → Y`. The theorem
`baseChange_descend` proves that its base change equals the given `g`,
and `descend_unique` and `existsUnique_hom` prove uniqueness with this
recovery property. The parametrization `p` and the morphism `h` need
not preserve the group laws.

The implementation applies
`AlgebraicGeometry.AffineEmbeddingDescent.descendHom` to the underlying
map from `F(H.X)` to `Y.X`. Its projection identity gives one component
of `pullback_overHom`; the other component is the fact that `g` is a
morphism over `K`. Extensionality for the actual pullback therefore
recovers the supplied extension-field underlying map. Pullback along
a field extension is faithful and monoidal, so
`GaloisCocharacterDescent.isMonHom_of_faithfulMap` reflects preservation
of the unit and multiplication. `Grp.homMk` packages the descended
scheme morphism with these laws. Faithfulness also proves uniqueness.
These equalities are equalities of actual morphisms and so hold on all
scheme tests.

No smoothness, connectedness, finite-type, separability, algebraicity,
perfectness, or characteristic assumption is made. The result neither
constructs the parametrization nor proves its dominance. It is a helper
for geometric character descent and does not supply a torus quotient,
unipotent kernel geometry, splitness, or the final unconditional
split geometric radical theorem.
