# Proof of `GeneralLinearRootDatumStatement`

Worker 274.

`Langlands.GroupScheme.generalLinearRootDatum : GeneralLinearRootDatumStatement`
proves the published statement of the module
`Langlands.GroupScheme.Reductive.RootDatumStatement`. For every field `k` and
every finite `n` with decidable equality, it establishes six facts about the
diagonal torus `D = GeneralLinear.diagonalTorus n k` of `GL_n`. These are Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups` (printed
page = PDF page − 16):

- Example 17.88, printed p.380 (PDF 396): `D_n` is maximal in `GL_n`, being
  its own centralizer;
- Example 21.6, printed p.426 (PDF 442): the roots of `(GL_n, D_n)` are
  `χ_i − χ_j` (`i ≠ j`), with `D_n` acting on `E_ij` through `χ_i − χ_j`;
- Example 21.40, printed p.436 (PDF 452): the permutation matrices normalize
  `D_n` and give `W(GL_n, D_n) ≅ S_n`.

Milne works with algebraic groups over a field and checks the examples by
hand. The formulation proved here is **derived**: it is stated for an arbitrary
field `k` and an arbitrary finite index type `n`. Maximality is the published
`IsMaximalTorus`, which is about factorizations through closed commutative group
schemes. The weight spaces of the published `weightSpace` are tested over all
commutative `k`-algebras. A normalizing point is a `k`-point whose conjugation
restricts to an automorphism of `D` as a morphism of group schemes, so on points
over every test scheme. Finally, the root datum is the Mathlib `RootDatum`
`GeneralLinear.rootDatum n k`, related to `D` through the published
`IsRootDatumOf`, and the Weyl image is compared with the range of the published
`GeneralLinear.permutationAction n k`. The Lean proof is assembled from the
helper modules below, whose Markdown describes their arguments.

1. `IsMaximalTorus D`: `isMaximalTorus_diagonalTorus` (module
   `GeneralLinearMaximal`). It uses the closed-subgroup property
   `isClosedSubgroup_diagonalTorus` (module `GeneralLinearDiagonal`), proved by
   identifying `D` with the spectrum of the coordinate ring of `GL_n` modulo the
   off-diagonal entries. Maximality is a dual-number commutation argument.
2. The roots of `D` are the characters `e_i − e_j` with `i ≠ j`:
   `roots_diagonalTorus` (module `GeneralLinearRoots`). The proof computes the
   actual adjoint action over all test algebras in matrix coordinates, and
   tests with one-variable Laurent points.
3. `IsRootDatumOf D (GeneralLinear.rootDatum n k)`: `isRootDatumOf_rootDatum`
   in this module. The pairing condition holds by definition. The range of the
   roots is identified with `roots D` through
   `characterLatticeEquiv_rootDatum_root` and `roots_diagonalTorus`. For each
   root `eᵢ − eⱼ`, the permutation matrix of the transposition `(i j)`
   normalizes `D` through `torusPerm (i j)` (`isNormalizingPoint_permPoint`).
   Its action `characterAut` is `permutationAction (i j)`
   (`characterAut_torusPerm`), which is the reflection of the root
   (`rootDatum_reflection`).
4. `(GeneralLinear.rootDatum n k).IsReduced`: `rootDatum_isReduced` in this
   module. If two roots are linearly dependent over `ℤ`, their coordinate
   vectors `eₐ − e_b` and `e_c − e_d` are too, since linear independence is
   preserved by the linear equivalence `characterCoordEquiv`. By
   `LinearIndependent.pair_iff` this gives a nontrivial relation.
   `rootCoord_eq_or_eq_neg` evaluates it at the four indices and concludes
   `(c, d) = (a, b)` or `(c, d) = (b, a)`. In the second case the root is the
   negative (`rootCoord_swap_eq_neg`).
5. `weylImage D = (GeneralLinear.permutationAction n k).range`:
   `weylImage_diagonalTorus` (modules `GeneralLinearWeyl` and
   `GeneralLinearNormalizer`). Permutation matrices give `⊇`. The inclusion `⊆`
   holds because every normalizing point is a monomial matrix and acts through
   a coordinate permutation.
6. `GeneralLinear.permutationAction n k` is injective:
   `permutationAction_injective` in this module. If `w` acts trivially, then
   evaluating at the character with coordinates `e_c` gives `e_c(w c) = 1`, so
   `w c = c`.

The proof imports the Library statement module unchanged. Its helper modules are
`GeneralLinearDiagonal`, `GeneralLinearMaximal`, `GeneralLinearWeyl`,
`GeneralLinearNormalizer` and `GeneralLinearRoots`, all in
`Langlands.GroupScheme.Reductive`. It also uses Worker 339's
`Langlands.GroupScheme.Lie.GeneralLinearAdjoint`.

## Authorship

Worker 274 wrote the Lean proof and the helper modules (shared draft revision 1
of task `cf9845bb-6399-4e65-9860-160b16c1da02`). Worker 1173 recompiled them
unchanged, checked the Milne locators against the registered PDF, and added the
source list, the paragraph on derived formulations and this section to the
Markdown.
