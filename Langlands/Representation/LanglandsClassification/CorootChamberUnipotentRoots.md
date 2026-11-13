# Roots positive on a coroot chamber are the roots in `N`: proof

Module `Langlands.Representation.LanglandsClassification.CorootChamberUnipotentRoots`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.

The module proves the published statement
`Langlands.GroupScheme.CorootChamberUnipotentRootsStatement` (Renard V.3.17)
as the theorem

```lean
theorem corootChamberUnipotentRoots : CorootChamberUnipotentRootsStatement.{u}
```

It adds no hypothesis. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`. The helper lemmas are in the namespace
`Langlands.GroupScheme.CorootChamberUnipotentRoots`.

Worker 128 wrote this proof under task `e341f206-3629-42d9-b9d7-2d86f3bddd89`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The lemma is
V.3.17, printed p.114 / PDF p.120. The statement's Markdown quotes it.

Renard's proof writes every root and its coroot in the simple roots and simple
coroots, with coefficients of one sign. The Lean proof takes a different route:

- It never expands a coroot in the simple coroots. The reflection data `D` alone
  does not give that expansion.
- It uses a Weyl-invariant form instead, which exists because the relative Weyl
  group is finite.

## The proof

Notation:

- `G`, `i : T → G` and `ν` are as in the statement.
- `x` is a point of the chamber and `r` is a relative root.
- `ř = D.coroot r`.
- `⟨x, ř⟩` is `RealTorusSpace.pair T x (1 ⊗ ř)`.
- `r'` is `1 ⊗ r` in the real character space `Vstar T = ℝ ⊗[ℤ] X*(T)`.

### Step 1: the roots in `N` (`mem_subgroupRelativeRoots_standardUnipotent_iff`)

Hypotheses: `T` is split, `G` is smooth and affine, and `ν` is generic. The
relative roots are stable under negation. `ζ` is a standard cocharacter of `J`
(`IsStandardCocharacter i ν J ζ`).

Conclusion: `r ∈ subgroupRelativeRoots i (standardUnipotent i ν J)` if and only if
`r ∈ relativeRoots i` and `0 < ⟨r, ζ⟩`.

- **(→)** `standardUnipotent i ν J ≤ Dynamic.unipotent (ζ ≫ i)`
  (`standardUnipotent_le_dynamicUnipotent`), and `subgroupRelativeRoots` is
  monotone. The published `RelativeRoot.subgroupRelativeRoots_dynamicUnipotent`
  says that the roots in `Dynamic.unipotent (ζ ≫ i)` are the relative roots `α`
  with `⟨α, ζ⟩ > 0`.
- **(←)** Since `r` is a relative root, it is nonzero and has a nonzero
  eigenvector `X` in the Lie algebra
  (`RelativeRoot.mem_relativeRoots_iff_actionWeightSupport_conjugation_top`). It
  remains to show that `X` lies in `standardUnipotent i ν J`, that is, in
  `Dynamic.unipotent (η ≫ i)` for every standard cocharacter `η` of `J`
  (`mem_standardUnipotent`).
  1. Standard cocharacters of one `J` give every relative root the same sign
     (`IsStandardCocharacter.haveSameRelativeRootSigns`, using genericity and
     negation stability). So `⟨r, η⟩ > 0`.
  2. The third component of the published
     `RelativeRoot.dynamicUnipotent_semigroupData` says that the dual-number
     points of `Dynamic.unipotent (η ≫ i)` coming from the Lie algebra are
     exactly `semigroupWeightSpan … (positiveSemigroup η)`.
  3. That span is the supremum of the weight spaces of the characters positive
     on `η`, so it contains the weight space of `r`, and hence `X`.

### Step 2: the averaged form (`averagedForm`)

`relativeWeylGroup i` acts on `Vstar T` through `relativeWeylFullRealAction i`.
This group is finite, and when it carries a `Fintype` instance the module
defines the real bilinear form

`B(x, y) = Σ_w ⟨w x, ν⟩ ⟨w y, ν⟩`,

where `⟨·, ν⟩` pairs with `1 ⊗ ν`. The definitions are `weylNuFunctional` and
`averagedForm`, and `averagedForm_apply` unfolds `B`. Its properties:

- **Invariance** (`averagedForm_invariant`): `B(u x, u y) = B(x, y)`. The proof
  reindexes the sum by `w ↦ w u`, using that the action is a monoid hom.
- **Reflections** (`reflection_apply`): the image of the normalizer point
  `D.representative r` in the Weyl group acts by `x ↦ x - ⟨x, ř⟩ r'`. On pure
  tensors this is `D.action`; the general case follows by induction on tensors.
- **Coroot pairing** (`coroot_pair_mul_form`):
  `⟨x, ř⟩ B(r', r') = 2 B(x, r')`.
  1. Apply invariance to the reflection `s` of `r` and the pair `(x, r')`.
  2. Since `⟨r', ř⟩ = 2` (`D.pair_self`), we have `s r' = -r'` and
     `s x = x - ⟨x, ř⟩ r'`.
  3. Expanding bilinearly gives `-B(x, r') + ⟨x, ř⟩ B(r', r') = B(x, r')`.
- **Positivity** (`averagedForm_root_pos`): `B(r', r') > 0`. The `w = 1` term of
  the sum is `⟨r, ν⟩² > 0`, because `ν` is generic, and every other term is a
  square.
- **Signs** (`coroot_pair_pos_iff`, `coroot_pair_eq_zero_iff`): the two facts
  above show that `⟨x, ř⟩ > 0 ↔ B(x, r') > 0` and `⟨x, ř⟩ = 0 ↔ B(x, r') = 0`.

### Step 3: induction over positive roots (`averagedForm_sign_of_positive`)

Let `x` satisfy the chamber conditions for `D` and `J`, and let `ζ` be a standard
cocharacter of `J`. Every positive root `β` then satisfies both
`0 ≤ B(x, 1 ⊗ β)` and `B(x, 1 ⊗ β) > 0 ↔ ⟨β, ζ⟩ > 0`.

The proof is the published `positiveRelativeRoots_induction`:

- **Simple `α ∈ J`.** `⟨x, α̌⟩ = 0` gives `B(x, 1 ⊗ α) = 0`, and `⟨α, ζ⟩ = 0`.
- **Simple `α ∉ J`.** `⟨x, α̌⟩ > 0` gives `B(x, 1 ⊗ α) > 0`, and `⟨α, ζ⟩ > 0`.
- **Sums.** `B(x, 1 ⊗ ·)` and `⟨·, ζ⟩` are additive. Both are nonnegative on
  positive roots (`IsStandardCocharacter.pairing_nonneg_of_positive` for `ζ`). A
  sum of two nonnegative terms is positive exactly when one of the terms is.

### Step 4: the theorem (`corootChamberUnipotentRoots`)

1. From `hG` and `hi` we get the instances, and `T` is split.
2. The relative Weyl group is finite (`IsConnectedReductive.finite_relativeWeylGroup`).
3. The relative roots are finite (`IsSplitTorus.finite_relativeRoots`), so a
   standard cocharacter `ζ` of `J` exists
   (`RelativeRootReflectionData.exists_standardCocharacter`).
4. Negation stability comes from `RelativeRootReflectionData.neg_mem_relativeRoots`.
5. Step 1 rewrites the right side as `r ∈ relativeRoots i ∧ 0 < ⟨r, ζ⟩`.
6. The chamber element `x` is the restriction of a point `y` along the identity
   of `T`. This restriction is the identity (`restrictReal_id_apply`, by tensor
   induction and `characterRestrict_id`), so `y = x`.
7. Step 2 rewrites the left side as `B(x, r') > 0`.
8. Genericity gives two cases:
   - **`⟨r, ν⟩ > 0`.** `r` is positive and Step 3 gives the equivalence.
   - **`⟨r, ν⟩ < 0`.** `-r` is a positive root. By Step 3, `B(x, r') ≤ 0` and
     `⟨r, ζ⟩ ≤ 0`, so both sides are false.

## Remarks

- The statement quantifies over all relative roots, including non-reduced ones
  (see the statement's "Formal choices"). The proof covers them without separate
  treatment: no reducedness is used anywhere.
- Finiteness of the relative Weyl group is the only reductive-group input on the
  coroot side, apart from the reflection data `D`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.CorootChamberUnipotentRootsStatement` | the target statement, `restrictedCorootChamber`, `RelativeRoot.subgroupRelativeRoots` |
| `Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness` | `IsConnectedReductive.finite_relativeWeylGroup` |
| `Langlands.GroupScheme.Rational.ReflectionStandardCocharacter` | `RelativeRootReflectionData.exists_standardCocharacter` and, through it, `RelativeRootReflectionData.neg_mem_relativeRoots` |
| `Langlands.GroupScheme.Rational.PositiveRootInduction` | `positiveRelativeRoots_induction`, `IsStandardCocharacter.haveSameRelativeRootSigns`, `IsStandardCocharacter.pairing_nonneg_of_positive` |
| `Langlands.GroupScheme.Rational.DynamicPositiveSemigroup` | `RelativeRoot.dynamicUnipotent_semigroupData` |
| `Langlands.GroupScheme.Rational.RootSupportFiniteness` | `IsSplitTorus.finite_relativeRoots` |
