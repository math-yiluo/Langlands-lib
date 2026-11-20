# Characterizations of trigonalizable groups (Milne 16.2): proof

Author: Worker 158.

`Langlands.GroupScheme.trigonalizableCharacterization` proves exactly the
Library proposition `Langlands.GroupScheme.TrigonalizableCharacterizationStatement.{u}`
(module [`CharacterizationStatement`](CharacterizationStatement.md)) at an
arbitrary universe `u`. The statement and its meaning are unchanged: for a
field `k` and a group scheme `G` over `Spec k` that is locally of finite type
and affine, `IsTrigonalizable G` is equivalent to (b) the existence of stable
maximal flags in every matrix representation, to (c) the existence of a
closed embedding into the upper triangular group `T_N` for some `N`, and to
(d) the existence of a normal unipotent closed subgroup `U` with an fppf
quotient `G ⟶ D(Λ)` by `U`, `Λ` finitely generated.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

After introducing `k`, `G` and the two instances, the proof combines four
theorems from the helper modules of this submission:

- (a) ⇔ (b) is `Trigonalizable.isTrigonalizable_iff_exists_stableFlag`
  (module [`Flag`](Flag.md)), whose statement is literally the first
  conjunct.
- (a) ⇒ (c) is `Trigonalizable.exists_closed_triangular_of_isTrigonalizable`
  (module [`TriangularEmbedding`](TriangularEmbedding.md)).
- (c) ⇒ (d) is
  `Trigonalizable.exists_unipotent_diagonalizable_quotient_of_closed_triangular`
  (module [`UnipotentQuotient`](UnipotentQuotient.md)), applied to the `N`
  and `j` given by (c).
- (d) ⇒ (a) is
  `Trigonalizable.isTrigonalizable_of_unipotent_diagonalizable_quotient`
  (module `UnipotentQuotient`), applied to the data given by (d).

The second conjunct is then (a) ⇒ (c) together with
(c) ⇒ (a) := (d) ⇒ (a) ∘ (c) ⇒ (d). The third conjunct is
(a) ⇒ (d) := (c) ⇒ (d) ∘ (a) ⇒ (c) together with (d) ⇒ (a).

The helper modules, in import order:

1. [`StableLines`](StableLines.md): comparison of stable lines (tested on
   all schemes) with stable subspaces (tested on affine points through
   linear functionals), transport of stable lines along restriction and
   intertwiners, and the vanishing of matrix coefficients that kill a stable
   subspace.
2. [`Flag`](Flag.md): (a) ⇔ (b), by induction on the dimension.
3. [`TriangularEmbedding`](TriangularEmbedding.md): (a) ⇒ (c), using a
   closed embedding into `GL_N`, a stable maximal flag and an adapted basis.
4. [`UnipotentQuotient`](UnipotentQuotient.md): (c) ⇒ (d), with `U` the
   kernel of the diagonal projection, and (d) ⇒ (a), through the vectors
   fixed by `U` and descent to `D(Λ)`.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), Proposition 16.2,
pp.324–325 (source ID `milne-2017-algebraic-groups`). The Lean proof uses
the cycle (a) ⇒ (c) ⇒ (d) ⇒ (a) together with (a) ⇔ (b). Milne's proof uses
the cycle (a) ⇒ (b) ⇒ (c) ⇒ (d) ⇒ (a). The individual steps follow his
arguments, as described in the helper modules.
