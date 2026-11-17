# Group-like elements of graded cocommutative bialgebras

Worker 603 wrote this module for Task 6776 (extensions of groups of
multiplicative type over a field). Its results are internal helpers. No
external source is formalized here.

Let `K` be a field and `A` a commutative `K`-bialgebra. A bialgebra map
`π : A → K[N]` to the group algebra of a commutative group `N` defines an
`N`-grading of `A`, with homogeneous components `grade π n`
([`GroupAlgebraCoaction`](GroupAlgebraCoaction.md)). Geometrically, `Spec A` is
a group `G` and `Spec π` is a diagonalizable subgroup `D(N)` of `G`, acting by
right translation.

The module proves two facts:

1. If `A` is cocommutative (`G` is commutative) and `K` is algebraically
   closed, every nonzero homogeneous component contains a group-like element.
2. In a Hopf algebra, suppose every degree contains a group-like element and
   the degree-zero component lies in the span of the group-like elements.
   Then the group-like elements span `A`.

Together, these show that a cocommutative Hopf algebra over an algebraically
closed field, graded by a surjective `π` whose degree-zero component is
spanned by group-like elements, is spanned by group-like elements
(`span_isGroupLikeElem_eq_top`). Geometrically: over an algebraically closed
field, a commutative extension of a diagonalizable group by `D(N)` is again
diagonalizable. The extension is diagonalizable when its degree-zero part, the
coordinate ring of the quotient, is spanned by group-like elements.

## Contents

### Common eigenvectors (`Langlands.CommonEigenvector`)

* `exists_mem_forall_eq_smul`: over an algebraically closed field, let `S` be a
  set of pairwise commuting endomorphisms of a vector space `V`, and `W` a
  nonzero finite-dimensional subspace preserved by every member of `S`. Then
  `W` contains a nonzero common eigenvector of `S`. The family `S` may be
  infinite.

  Proof: strong induction on `finrank W`. If every member of `S` acts on `W`
  as a scalar, any nonzero vector of `W` works. Otherwise some `f ∈ S` is not
  a scalar on `W`. Its restriction to `W` has an eigenvalue `μ`
  (`Module.End.exists_eigenvalue`). The subspace
  `W' = W ⊓ eigenspace f μ` is nonzero, strictly smaller than `W`, and
  preserved by every `g ∈ S`, because `g` commutes with `f`. The induction
  hypothesis applies to `W'`.

### Tensors over a field (`Langlands.GroupAlgebraCoaction`)

* `eq_zero_of_forall_rid_lTensor`: over a field, an element `t` of `X ⊗ A` is
  zero if `(id ⊗ f) t = 0` in `X ⊗ K ≅ X` for every linear form `f` on `A`.
  Choose a basis `b` of `A`. The coordinates of `t` under Mathlib's
  `TensorProduct.equivFinsuppOfBasisRight b` are the elements
  `(id ⊗ b.coord i) t`.

### Eigenvectors of right translations are group-like up to a scalar

Recall from [`GroupAlgebraCoaction`](GroupAlgebraCoaction.md) the right action
`ract f a = ∑ f(a₂) a₁` and the left action `lact f a = ∑ f(a₁) a₂` of a linear
form `f` on a coalgebra.

* `apply_ract`: `φ (ract f a) = f (lact φ a)`. Both sides equal `∑ φ(a₁) f(a₂)`.
* `exists_isGroupLikeElem_smul_of_forall_ract`: let `v ≠ 0` satisfy
  `ract f v ∈ K v` for every linear form `f`. Then some scalar multiple of `v`
  is group-like.

  Proof: choose `φ` with `φ v = 1` (`Module.forall_dual_apply_eq_zero_iff`)
  and put `a = lact φ v`. For every `f`, write `ract f v = c v`. Then
  `f a = φ (ract f v) = c`, so `(id ⊗ f)(Δv − v ⊗ a) = c v − c v = 0`. By
  `eq_zero_of_forall_rid_lTensor`, `Δv = v ⊗ a`. The counit identity
  `(ε ⊗ id) Δv = v` gives `ε(v) a = v`, so `ε(v) ≠ 0` and
  `a = ε(v)⁻¹ v`. Then `ε(a) = 1` and `Δa = ε(v)⁻¹ v ⊗ a = a ⊗ a`.

### Cocommutative coalgebras

* `conv_comm`: in a cocommutative coalgebra (Mathlib's `Coalgebra.IsCocomm`),
  the convolution `conv f g` of linear forms is commutative. Compose with the
  swap of tensor factors and use `Coalgebra.comm_comul`.
* `ract_comp_ract_comm`: the right translations `ract f` and `ract g`
  commute. This follows from the Library's `ract_ract`,
  `ract f (ract g a) = ract (conv f g) a`.

### Graded bialgebras

* `grade_ne_bot_of_surjective`: if `π` is surjective, every component
  `grade π n` is nonzero. Take `a` with `π a = Xⁿ`. The counit of the
  component `proj π n a` is the coefficient `(π a)ₙ = 1` (`counit_proj`).
* `ract_mem_grade` (cocommutative `A`): right translations preserve every
  component. Since `proj π n = ract (coeffForm π n)` and right translations
  commute, `proj π n (ract f a) = ract f (proj π n a) = ract f a` for
  `a ∈ grade π n`.
* `exists_isGroupLikeElem_mem_grade` (cocommutative `A`, algebraically closed
  `K`): if `grade π n ≠ ⊥`, it contains a group-like element.

  Proof: take `x ≠ 0` in `grade π n` and let `W` be the span of all
  `ract f x`. Then:
  - `W` lies in `grade π n`, by `ract_mem_grade`.
  - `W` contains `x = ract ε x` (`ract_counit`).
  - `W` is finite-dimensional. For a representation
    `Δx = ∑ᵢ xᵢ ⊗ yᵢ` (`Coalgebra.Repr.arbitrary`), every `ract f x` lies in
    the span of the `xᵢ` (`ract_apply`).
  - `W` is preserved by every `ract g`, since `ract g (ract f x) = ract (conv g f) x`.

  The operators `ract f` commute, so `exists_mem_forall_eq_smul` gives a
  common eigenvector `w ∈ W`. By
  `exists_isGroupLikeElem_smul_of_forall_ract`, some multiple `c w ∈ grade π n`
  is group-like.

### Graded Hopf algebras

* `mem_span_isGroupLikeElem_of_mem_grade`: let `g ∈ grade π n` be group-like
  and suppose `grade π 0` lies in the span of the group-like elements. Then so
  does every `a ∈ grade π n`. The element `g` is a unit
  (`IsGroupLikeElem.isUnit`), and its inverse has degree `-n`
  (`inv_mem_grade`). So `a g⁻¹` has degree `0`, and `a = (a g⁻¹) g`.
  Right multiplication by `g` maps the span of the group-like elements into
  itself, because products of group-like elements are group-like
  (`IsGroupLikeElem.mul`).
* `span_isGroupLikeElem_eq_top_of_forall_grade`: if every degree contains a
  group-like element and `grade π 0` lies in the span of the group-like
  elements, then the group-like elements span `A`. Every `a` is the sum of
  its components `proj π n a` (`sum_proj`).
* `span_isGroupLikeElem_eq_top`: for a cocommutative Hopf algebra over an
  algebraically closed field and a surjective `π` whose degree-zero component
  lies in the span of the group-like elements, the group-like elements span
  `A`. Combine the two previous results with `grade_ne_bot_of_surjective`.

## Provenance

Internal to this project. The argument is the standard proof that a
commutative algebraic group is diagonalizable when its coordinate ring is a
sum of one-dimensional comodules, here applied to the components of the
`N`-grading: in a finite-dimensional comodule, the commuting operators have a
common eigenvector, and that eigenvector spans a one-dimensional subcomodule,
hence is a group-like element up to a scalar. Compare Milne, *Algebraic
Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 12.8 (printed
p.233): an algebraic group is diagonalizable exactly when its coordinate ring
is spanned by group-like elements. No result of this module is attributed to
that source.
