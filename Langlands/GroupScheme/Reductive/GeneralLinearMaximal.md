# The diagonal torus of `GL_n` is a maximal torus

Worker 274.

This is a helper module for the proof of `GeneralLinearRootDatumStatement`. It proves
`isMaximalTorus_diagonalTorus k`: over a field `k`, the diagonal torus is a
maximal torus in the sense of `IsMaximalTorus` (Milne, Example 17.88, printed
p.380, PDF 396). Milne's argument is that `D_n` is its own centralizer, because a
matrix commuting with the matrices `I + E_ii` is diagonal. The Lean proof
follows this idea but tests with the dual numbers instead. It shows directly
that any commutative group scheme through which the diagonal torus factors maps
into diagonal matrices. The formulation through `IsMaximalTorus` over an
arbitrary field, with factorizations through closed commutative group schemes,
is derived; the key lemma below even holds over any base ring `R`.

## The key lemma

Let `T'` be a commutative group scheme over `Spec R`, `i' : T' ⟶ GL_n`, and
`f : D_n ⟶ T'` with `f ≫ i' = diagonalTorus` (any base ring `R`).

- `isDiagonalGL_affinePointsEquiv`: for every algebra `B` and every `B`-point
  `y` of `T'`, the matrix of `i'(y)` is diagonal. Take `B' = DualNumber B`, the
  point `y'` of `T'` induced by `B → B'`, and the point `t` of `D_n` with
  coordinates `(1, …, 1 + ε, …, 1)` (unit `onePlusEps`) at position `a`.
  Commutativity of `T'` gives `y' f(t) = f(t) y'`. Applying `i'` and comparing
  the `(a, b)` entries, for `a ≠ b`, gives `m = (1 + ε) m` for the image `m` of
  the `(a, b)` entry of `i'(y)`. The computation is done in global sections and
  transported to `B'` through the published `affineSectionsIso`. Hence `ε m = 0`
  and `m = 0` (`eq_zero_of_eps_mul_inl`). The helper
  `affinePointsEquiv_eq_map_pointsEquiv` relates the affine and global-section
  coordinates of `GL_n`.
- `isDiagonalGL_universal`: if `T'.X` is affine, the universal point of `T'`
  maps to a diagonal matrix. Indeed `T'.X ≅ algSpec B` (Mathlib
  `essImage_algSpec`), so the universal point is a restriction of an affine
  point.
- `universalLift`, `liftPoints` and `liftHom` build the homomorphism
  `liftHom : T' ⟶ D_n` with `liftHom ≫ diagonalTorus = i'` (`liftHom_comp`). It
  is defined on points by composing with the factorization of the universal
  point. It is multiplicative because `diagonalTorus` is a monomorphism.
- `isIso_of_comp_eq_diagonalTorus`: if moreover `i'` is a closed subgroup, then
  `f` is an isomorphism with inverse `liftHom`. A closed immersion into the
  affine `GL_n` has affine source, and it is a monomorphism. The two composites
  are identities after cancelling the monomorphisms `diagonalTorus` and `i'`.

## Maximality

`isMaximalTorus_diagonalTorus k` combines three facts:
- the split torus is a torus (`IsSplitTorus.isTorus`);
- `isClosedSubgroup_diagonalTorus`;
- `isIso_of_comp_eq_diagonalTorus`. The torus hypothesis on `T'` is not needed.
