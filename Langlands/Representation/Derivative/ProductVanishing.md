# Vanishing and nonvanishing of products

Module `Langlands.Representation.Derivative.ProductVanishing`, namespace
`Langlands.Derivative.ProductVanishing`.

These are elementary facts about the published product functors. They are used
by the proof of Zelevinsky's Theorem 6.2 to compare levels of products.

1. A left or right mixed product with a zero factor is zero.
2. A binary normalized product with a zero factor is zero.
3. A normalized block product, or a binary normalized product, of nonzero
   factors is nonzero.

## Provenance

This is internal derived material. Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I*
(`bernstein-zelevinsky-1977-induced-i`, §4.12–§4.14) and Zelevinsky
(`zelevinsky-1980-induced-ii`, §4.13, §5) use these facts without comment. In
Lean they follow from the published function models: values of mixed products
lie in `X.1 ⊗ X.2`, and the slot subrepresentations of normalized products are
nonzero. No source result is formalized here as such.

## Adapted code and attribution

Three declarations of this module reuse published Library code by Worker 745
from `Langlands/Representation/Classification/TwoSupercuspidalBinaryProductBridge.lean`
(namespace `Langlands.Classification.BinaryProductBridge`,
lines 76–115 at Library commit `a9fde216`). Worker 745 is therefore a coauthor
of this module.

- `subsingleton_of_isZero` and `isZero_of_subsingleton` are copied from the
  declarations of the same names. The statements and proofs are unchanged;
  only the namespace differs and the field `F` is implicit here.
- `subsingleton_binary` is adapted from `subsingleton_rankCast_product`. It
  keeps the case split and the call to
  `isZero_binaryNormalizedProductFunctor_obj`, but it is stated for the binary
  product itself, without the rank cast, and for a pair `X`.

The code is copied rather than imported. This keeps
`TwoSupercuspidalBinaryProductBridge`, a two-supercuspidal product module, out
of the import closure audited in `LevelCalculus.md`.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and `T : F.TopologicalData`
are fixed, and `T.topology` is installed. Factor carriers are in `Type uV`;
the product carriers are in `Type (max uF uV)`, as in the published functors.
`GeneralLinear k F.Carrier` is `GL_k`; `mirabolic r F.Carrier` is `P_(r+1)`.

- `T.leftMixedProductFunctor k r` sends a pair `(X.1, X.2)` of a `GL_k`
  representation and a `P_(r+1)` representation to their left mixed product on
  `P_(k+r+1)` (BZ77 §4.12, `Langlands.Representation.Mirabolic.MixedProducts`).
- `T.rightMixedProductFunctor k r` sends a pair of a `P_(r+1)` representation
  and a `GL_k` representation to their right mixed product on `P_(k+r+1)`.
- `T.binaryNormalizedProductFunctor a b` is the published normalized product
  `GL_a × GL_b → GL_(a+b)`. When `a = 0` or `b = 0` it is the published tensor
  model.
- `T.normalizedProductInductionFunctor B` is normalized parabolic induction of a
  family of factors indexed by the blocks of `B : BlockShape n`.

## Declarations

- `subsingleton_leftMixed_of_tensor`, `subsingleton_rightMixed_of_tensor`: if
  `X.1 ⊗[ℂ] X.2` is a subsingleton, then so is the left (respectively right)
  mixed product of `X`. Proof: the published evaluation maps
  `leftMixedEval`/`rightMixedEval` into functions with values in
  `X.1 ⊗ X.2` are injective (`leftMixedEval_injective`,
  `rightMixedEval_injective`).
- `subsingleton_leftMixed`, `subsingleton_rightMixed`: if either factor is a
  subsingleton, the mixed product is a subsingleton (the tensor product is
  then a subsingleton).
- `subsingleton_of_isZero`, `isZero_of_subsingleton`: for a smooth
  representation of `GL_n`, being a zero object of the category is equivalent
  to having a subsingleton carrier (the two directions).
- `subsingleton_binary`: if either factor is a subsingleton, the binary
  normalized product is a subsingleton. Proof: the published
  `isZero_binaryNormalizedProductFunctor_obj`.
- `nontrivial_tensor`: the tensor product over `ℂ` of two nontrivial complex
  vector spaces is nontrivial.
- `top_ne_bot_of_nontrivial`, `nontrivial_of_top_ne_bot`: for a representation
  `ρ` on `V`, the subrepresentation lattice satisfies `⊤ ≠ ⊥` iff `V` is
  nontrivial (the two directions).
- `nontrivial_normalizedProduct B A hA j`: let `B : BlockShape n` have at least
  one block (witnessed by `j : Fin B.length`), and let every factor `A i` be
  nontrivial. Then the normalized block product
  `(T.normalizedProductInductionFunctor B).obj A` is nontrivial. Proof: the
  published `Parabolic.normalizedProductSlotSubrepresentation_ne_bot` with the
  subrepresentation `⊤` in slot `j`, and
  `normalizedProductSlotSubrepresentation_top`.
- `nontrivial_binary`: if both factors are nontrivial, the binary normalized
  product is nontrivial. Three cases. If `a = 0` or `b = 0`, the product is the
  published tensor model `ULift (X.1 ⊗ X.2)`, and `nontrivial_tensor` applies.
  If `0 < a` and `0 < b`, the product is the block product of the binary shape
  (`binaryNormalizedProductFunctor_of_pos`), and `nontrivial_normalizedProduct`
  applies.
