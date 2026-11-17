# The mixed Euler coefficient of pulled-back line bundles on Hom

Module `Langlands.AbelianScheme.HomPullbackMixedEulerCube`.

## Content

Let `k` be a field and let `A`, `B` be abelian schemes over `Spec k`. Fix
line bundles `LA` on `A` and `LB` on `B`, and a natural number `g`.

- `homMixedEuler LA LB g : (A ⟶ B) → ℚ` sends an actual homomorphism `f` to
  `mixedLineBundleEulerCoefficient A.X.hom LA ((LineBundle.pullback (hom f)).obj LB) g`.
  This is the actual mixed Euler coefficient of the pullback `f^* LB`,
  computed with respect to `LA` and dimension truncation `g`.
- `exists_int_factorial_mul_homMixedEuler`: `g! · homMixedEuler LA LB g f`
  is an integer for every `f`.
- `homMixedEuler_cubeIdentity`: if `A` has relative dimension `d + 1`, then
  `homMixedEuler LA LB (d + 1)` satisfies
  `Langlands.Algebra.CubeQuadratic.CubeIdentity`, i.e. for all `f g h`,
  `q (f + g + h) + q f + q g + q h = q (f + g) + q (f + h) + q (g + h)`.
- `fg_comap_homToHom0_of_homMixedEuler_pos`: if `A` has relative dimension
  `d + 1` and `homMixedEuler LA LB (d + 1) f > 0` for every nonzero `f`, then
  for every finitely generated `ℚ`-submodule `V` of `Hom0 A B`, the preimage
  `(V.restrictScalars ℤ).comap homToHom0` is a finitely generated
  `ℤ`-module. This is the conclusion of `HomLocalLatticeStatement` for the
  pair `A`, `B`.

No ampleness is assumed in this module. Positivity enters only as the
hypothesis of the last theorem.

## Proof

The denominator bound is
`exists_int_factorial_mul_mixedLineBundleEulerCoefficient` from
`MixedEulerCoefficientDenominator`.

For the cube identity, put `a x := (groupHom x).hom.hom : A.X ⟶ B.X`. The
published balanced cube theorem `GroupScheme.fieldCubePullback`, applied to
`B` and the three maps `a f`, `a g`, `a h` from `A.X`, gives an isomorphism
of actual sheaf tensor products
`Q(fgh) ⊗ (Q f ⊗ (Q g ⊗ Q h)) ≅ Q(fg) ⊗ (Q(fh) ⊗ Q(gh))`. Here `Q x` is the
pullback of `LB` along `x.left` and products are pointwise products of
points. The sum `f + g` in `A ⟶ B` is by definition the pointwise product
`a f * a g`, so `Q(fg)` is definitionally the pullback of `LB` along
`hom (f + g)`, and likewise for the other terms. The published
`mixedLineBundleEulerPolynomial_iso` turns this isomorphism into an equality
of mixed Euler coefficients. The published tensor additivity
`mixedEulerCoefficientTensorAdditive` (valid since `A.X.left` is integral,
Noetherian and separated of topological dimension `d + 1`) splits both
sides, and `linarith` gives the identity.

The last theorem is
`Langlands.Algebra.CubeQuadratic.fg_comap_of_cubeIdentity` with
`N = (d + 1)!`. Since `Hom0 A B` is `ℚ ⊗[ℤ] (A ⟶ B)` and `homToHom0` is
`TensorProduct.mk ℤ ℚ (A ⟶ B) 1` by definition, the conclusion matches.

## Provenance

The source is J. S. Milne, *Abelian Varieties*, author revision of the 1986
article (registered as `milne-abelian-varieties-1986-author-2022`). For
abelian varieties and `g = dim A`, Riemann–Roch identifies `homMixedEuler`
with `(LA^{g-1} · f^* LB)/(g-1)!`, as recorded in the Library Markdown of
`MixedLineBundleEuler` (Milne, Theorem 17.3). That this is quadratic in `f`
reflects the theorem of the cube for pullbacks along sums of maps (Milne,
Corollaries 6.4–6.5, as recorded for `FieldCubePullbackStatement`). Using
this positive quadratic function in place of the degree polynomial of
Milne's proof of Theorem 12.5 is a derived construction internal to this
project. The Lean proof uses only actual Euler polynomials, so no
Riemann–Roch comparison is assumed or proved.
