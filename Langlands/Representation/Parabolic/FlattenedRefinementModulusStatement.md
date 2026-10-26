# Full modulus comparison for a flattened block refinement

`Langlands.Parabolic.FlattenedRefinementModulusStatement.{uF}` is the closed
proposition

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (n : ℕ) (B : GeneralLinear.BlockShape n) (S : BlockRefinement B),
  (T.composedLeviModulus B S).comp
    (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom =
      T.leviModulus (B.flatten S)
```

with `GeneralLinear` and `Geometric` open, so `BlockRefinement B` is
`Geometric.BlockRefinement B`. The module imports only
`Langlands.Representation.Geometric.FlattenedLevi` and
`Langlands.Representation.Parabolic.RefinementComposition`.

This module states the comparison; it does not prove it. Both sides are
monoid homomorphisms from `(B.flatten S).Levi F.Carrier` to `ℝ≥0ˣ`, the
units of the nonnegative reals, that is, the strictly positive reals. The
assertion is equality of these homomorphisms. No pointwise modulus equality,
scalar factor, chosen square root or normalization theorem appears among
its hypotheses.

## The groups and characters

Write `C = B.flatten S`. Its blocks are the fine blocks of `S`, listed
lexicographically: `C.length = ∑ i, (S i).length`, and the fine block `(i,j)`
is numbered `B.flattenBlockEquiv S ⟨i, j⟩`, where `B.flattenBlockEquiv S` is
`finSigmaFinEquiv`. The equivalence in the statement has direction

```lean
Geometric.flattenedLeviEquiv F.Carrier B S :
  C.Levi F.Carrier ≃* Geometric.refinedLevi F.Carrier B S
```

It groups the fine diagonal blocks of a flattened Levi element by outer
block, after the size transport along `B.flatten_size_flattenBlockEquiv S`.
It then embeds each group into `GL_{B.size i}` by the block diagonal
embedding of `S i`. The codomain is the published refined Levi subgroup of
`B.Levi F.Carrier`. So the left side pulls the composed character back to
the flattened product Levi along the forward equivalence. The published
`flattenedLeviEquiv_embedding` shows that the ambient `GL_n` matrix of the
image is the block diagonal embedding of the original element for `C`.

`T.composedLeviModulus B S` is defined in `Parabolic.RefinementComposition`
as the product `T.refinedOuterModulus B S * T.refinedLeviModulus B S`:

- The outer factor `T.refinedOuterModulus B S` is `T.leviModulus B` composed
  with the subgroup inclusion of `refinedLevi F.Carrier B S` into
  `B.Levi F.Carrier`. It accounts for the rectangular blocks that lie
  between distinct outer blocks.
- The inner factor `T.refinedLeviModulus B S` is the pointwise product over
  `i` of `T.leviModulus (S i)` composed with `refinedLeviBlock B S i`. That
  map extracts the `S i`-Levi coordinates of outer block `i`. This factor
  accounts for pairs of fine blocks inside one outer block.

For a block shape with sizes `d_i`, `T.leviModulus` (in `Group/GL/BlockModulus`)
is the product over `i < j` of

```text
|det(m_i)|_F ^ d_j / |det(m_j)|_F ^ d_i.
```

Each factor `|det(m_i)|_F` is `T.determinantNorm (d_i) (m i)`, that is,
`T.normalizedAbsUnits` applied to the determinant. For nonzero `x` this
absolute value is `q ^ (-ord_F(x))`, where `q` is the residue cardinality and
`ord_F` the published discrete valuation. The statement therefore compares
two explicit determinant products with the same normalization. Their
identification with Haar-measure scaling on unipotent radicals is a
separate matter that this statement does not address.

## The calculation a proof must supply

Fix `m : C.Levi F.Carrier` and write `φ = flattenedLeviEquiv F.Carrier B S`.
Put `d_ij = (S i).size j`, and let `a_ij` be the normalized determinant of
the fine block `m (B.flattenBlockEquiv S ⟨i, j⟩)`.

1. *Coordinates.* By `flattenedLeviEquiv_component`, the `(i,j)` inner block
   of `φ m` is that fine block reindexed by `finCongr` along the size
   equality. A simultaneous row and column reindexing preserves the
   determinant, so its normalized determinant is `a_ij`.
2. *Outer factor.* Outer block `i` of `φ m` is the block diagonal embedding
   of its inner blocks, so its normalized determinant is `∏ j, a_ij`. Also
   `∑ j, d_ij = B.size i` by `(S i).sum_eq`. Hence
   `T.refinedOuterModulus B S (φ m)` is the product over `i < k` of
   `(∏ j, a_ij) ^ (∑ l, d_kl) / (∏ l, a_kl) ^ (∑ j, d_ij)`.
3. *Inner factor.* `T.refinedLeviModulus B S (φ m)` is the product over `i`
   of the product over `j < l` of `a_ij ^ d_il / a_il ^ d_ij`.
4. *Flattened side.* `T.leviModulus C m` is the product, over pairs of fine
   blocks with `B.flattenBlockEquiv S ⟨i, j⟩ < B.flattenBlockEquiv S ⟨k, l⟩`,
   of `a_ij ^ d_kl / a_kl ^ d_ij`. Reindexing along `B.flattenBlockEquiv S`
   uses `flatten_size_flattenBlockEquiv` to identify the fine sizes. By
   `flattenBlockEquiv_lt_iff`, this order condition holds exactly when
   `i < k`, or `i = k` and `j < l`. These two cases are disjoint.
5. *Partition.* For a fixed pair `i < k` the factors form a rectangle in
   `(j,l)`, whose product in the commutative group `ℝ≥0ˣ` is the outer
   expression of step 2. The pairs with `i = k` and `j < l` give exactly
   the inner product of step 3.

Multiplying gives
`T.composedLeviModulus B S (φ m) = T.leviModulus C m` for every `m`, and
extensionality of monoid homomorphisms gives the displayed equality. The
Library module `Parabolic.FlattenedRefinementModulusCalculation` contains a
theorem, `Langlands.PadicField.TopologicalData.composedLeviModulus_flattened`,
whose conclusion is this equality for fixed parameters, proved along this
route. This statement module neither imports nor uses it. Proving the
closed proposition is left to a separate proof task.

The published `Langlands.Parabolic.RefinementCoordinatesModulusTheorem` is a
related statement. It compares `T.composedLeviModulus D S` with
`T.leviModulus B` pointwise, through `B.leviRefinementEquiv D S e hs`, for a
fine shape `B` related to `D` and `S` by explicit coordinate hypotheses
`e`, `hs` and `hc`; its equivalence runs from `B.Levi` to the refined
Levi. The present statement concerns the canonical fine shape
`B.flatten S` with the published `flattenedLeviEquiv` instead. It has no
coordinate hypotheses and states an equality of homomorphisms.

## Scope, including rank zero

The quantifiers cover every prime `p`, every `F : PadicField.{uF} p` with
topological data `T`, every rank `n`, every ordered block shape `B` of `n`
and every ordered block refinement `S`. Block sizes are positive by the
`BlockShape` structure, and there is no nonemptiness or positive-rank
hypothesis. At rank zero, positivity and `B.sum_eq` force `B.length = 0`,
so `C.length = 0`. Every product above is then empty and both characters
are the trivial character. The statement compares characters only and has
no representation or smoothness premise.

## Positive halves and inverse halves

These are consequences that are neither stated nor proved here. Both
`Jacquet.positiveHalfCharacter δ = (Units.map NNReal.sqrtHom.toMonoidHom).comp δ`
and `Jacquet.complexCharacter` compose a fixed homomorphism on the left, so
they commute with precomposition by `φ.toMonoidHom`. Once the full equality
is proved, rewriting with it therefore gives
`(T.composedLeviHalfModulus B S).comp φ.toMonoidHom = T.leviHalfModulus C`.
Likewise, `Jacquet.inverseHalfCharacter δ` is the pointwise inverse of
`complexCharacter (positiveHalfCharacter δ)`, so pulling back
`Jacquet.inverseHalfCharacter (T.composedLeviModulus B S)` along `φ` gives
`Jacquet.inverseHalfCharacter (T.leviModulus C)`. Neither step needs a sign
choice or a separate square-root compatibility hypothesis.

## Source and provenance

The mathematical motivation is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i` (SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`). We read
these passages directly and also checked the page images. PDF pages below
are counted from 1.

- §1.7 (printed p.444, PDF page 5) defines the module `mod_U` and gives
  `mod_{U'\U} = mod_U / mod_{U'}` for a closed subgroup `U'` of `U`.
  §1.8 on the same page puts its positive square root `mod_U^{1/2}` into
  the induction and localisation functors.
- Proposition 1.9(c) (printed p.445, PDF page 6) gives the composition
  identities for induction and Jacquet functors. The remark after it
  requires compatibility of the normalizing factors.
- §2.2 and Proposition 2.3(c) (printed p.446, PDF page 7) describe the
  standard Levi subgroups of `GL_n` by ordered partitions and their
  refinements, and give transitivity of normalized induction and Jacquet
  functors.

No errata for this source were found in the literature index or in the
public notes.

The source motivates the requirement that the normalizing characters are
compatible under refinement. It does not state this Lean formula. The
following are internal to this formulation: the coordinate presentation via
`flattenedLeviEquiv`, the determinant-product definitions of both
characters, their equality as homomorphisms into `ℝ≥0ˣ`, and the
inclusion of rank zero with empty products.
