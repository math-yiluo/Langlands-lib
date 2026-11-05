# Operations on algebraically bounded sets of rational points

This module proves elementary closure properties of the Library predicate
`IsAlgebraicallyBounded F X S` (from `AffineBoundedness.lean`) for a set `S` of
`F`-rational points of an affine `F`-scheme `X`. The predicate formalizes KP
Definition 2.2.1: every regular function `f` has a valuative bound
`v (f p) ≤ v b` with `b ≠ 0` on `S`. In KP's additive convention this says that
`ω (f(p))` is bounded below. All results are stated at arbitrary universe `u`, and
everything lies in namespace `Langlands.AlgebraicGeometry.PointTopology`.

## General field with a valuative relation

These results need only `[Field F] [ValuativeRel F]` and `[IsAffine X.left]`.

- `IsAlgebraicallyBounded.mono`: a subset of a bounded set is bounded, with the
  same bound for each function.
- `isAlgebraicallyBounded_empty`: the empty set is bounded, with bound `1`.
- `IsAlgebraicallyBounded.union`: the union of two bounded sets is bounded.
  For each function, take the larger of the two bounds (`vle_total`).
- `isAlgebraicallyBounded_singleton`: one point is bounded. Its own value
  `f p` is a bound when it is nonzero, and `1` is a bound otherwise.
- `algebraicBornology F X : Bornology (RationalPoint F X)` (definition): the
  four facts above are exactly the axioms of Mathlib's `Bornology.ofBounded`,
  so the algebraically bounded sets are the bounded sets of a bornology on
  `X(F)`. This is a repackaging of KP Definition 2.2.1, not a new notion. It is
  a plain definition, not a global instance, so it does not change the
  bornology of any existing type.
- `isBounded_algebraicBornology_iff`: a set is bounded for
  `algebraicBornology F X` if and only if it is algebraically bounded
  (`Bornology.isBounded_ofBounded_iff`).
- `Set.Finite.isAlgebraicallyBounded_biUnion`,
  `isAlgebraicallyBounded_iUnion`: finite unions (indexed by a finite set or
  a `Finite` type) of bounded sets are bounded. The proof is finite-set
  induction from the two previous facts.
- `Set.Finite.isAlgebraicallyBounded`: every finite set of points is bounded.
- `IsAlgebraicallyBounded.image`: for a morphism `f : X ⟶ Y` in `Over Spec F`
  between affine schemes, the image `(· ≫ f) '' S` of a bounded set is bounded.
  A regular function `a` on `Y` pulls back to `affineCoordinatePullback F f a` on
  `X`, and `rationalPointAlgebraHom_pullback` identifies its values. This is
  KP Fact 2.2.4. No finite-type hypothesis is needed here.
- `IsAlgebraicallyBounded.image_rationalPointsMap`: the special case of a
  group-scheme homomorphism `j : H ⟶ G`. Its rational point map
  `rationalPoints.map j` is composition with `j.hom.hom`.

## Nonarchimedean local fields

From here on `F` is a nonarchimedean local field (`IsNonarchimedeanLocalField F`,
either characteristic), and `RationalPoint F X` carries the canonical
`rationalPointTopology F X`.

- `isAlgebraicallyBounded_of_isCompact`: compact sets are bounded. Evaluation
  of a regular function is continuous. It is the composite of
  `rationalPointHomeomorph`, `affineSchemePointHomeomorph` and
  `AlgPoint.continuous_eval`. So `IsCompact.exists_valuative_bound` bounds its
  image. No finite-type hypothesis is used.
- `isAlgebraicallyBounded_iff_isCompact_closure` (for `LocallyOfFiniteType X.hom`):
  `S` is bounded if and only if its closure is compact. The forward direction is
  the Library's `IsAlgebraicallyBounded.isCompact_closure`. The reverse direction
  applies the previous lemma to the closure and then `mono`. This is the
  closure form of KP Fact 2.2.3.

For a group scheme `G` over `Spec F` with `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom`, `rationalPoints G` is a topological group
(`rationalPoint_isTopologicalGroup`). The group results follow:

- `IsAlgebraicallyBounded.mul`: if `S` and `T` are bounded, so is `S * T`. The
  closures are compact, so their product is compact (`IsCompact.mul`), hence
  bounded, and it contains `S * T`. This is the "if" direction of KP
  Lemma 2.2.6. KP proves that direction through the multiplication morphism
  `X × X → X`. The proof here instead uses compactness and the topological group
  structure, and therefore needs the local-field hypothesis.
- `IsAlgebraicallyBounded.inv`: `S⁻¹` is bounded, because the inverse of the
  compact closure is compact.
- `IsAlgebraicallyBounded.smul_set` and `IsAlgebraicallyBounded.mul_singleton`:
  left translates `g • S` and right translates `S * {g}` are bounded. Each is a
  product with a bounded singleton.

## Provenance and scope

The definition `algebraicBornology` and the results are internal: the
definition only repackages the Library predicate, and the results are
helper lemmas. They are derived from the Library's
definition of algebraic boundedness and from its compactness comparison
(`AffineBoundedCompactness.lean`, `BoundedSubgroupNormKernel.lean`) and point
transport (`AffineBoundedTransport.lean`) results. They correspond to KP
Definition 2.2.1, Facts 2.2.3 and 2.2.4 and the "if" direction of Lemma 2.2.6
(Kaletha–Prasad 2023, §2.2, printed pp. 70–71, PDF pp. 101–102). The converse
direction of Lemma 2.2.6 is not formalized. No statement about buildings,
fixers or Bruhat–Tits groups is made here.
