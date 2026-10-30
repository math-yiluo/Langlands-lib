# Swapping the factors of an irreducible equal-rank product

Author: Worker 1023.

`Langlands.Classification.IrreducibleTwoFactorProductSwap.{uF,uV} F T` is a
proposition definition. It names the irreducible equal-rank case of
Zelevinsky 1980, Theorem 1.9, printed p.174 (PDF p.11): if `α × β` is
irreducible then it is isomorphic to `β × α`. This module proves no theorem.

## Exact statement

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p` and compatible
topological data `T : F.TopologicalData`; the statement works under
`T.topology`. For every `k : ℕ` with `hk : 0 < k` and all smooth
representations `α β : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier)` such
that

- `α.IsIrreducible` and `β.IsIrreducible`, and
- the actual upper normalized product

  ```lean
  (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
    (twoBlockFactors hk hk α β)
  ```

  is irreducible (`IsIrreducible`),

there is an isomorphism, in the category of smooth representations of
`GL_{2k}(F)`, between that product and

```lean
(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
  (twoBlockFactors hk hk β α)
```

Here `Shahidi.twoBlocks k k hk hk` is the standard upper block shape `(k, k)`
and `twoBlockFactors hk hk α β` places `α` in the first (upper-left) block and
`β` in the second. The product is the Library's normalized parabolic induction
with positive half-modulus covariance and right translation, so the first
product is `α × β` and the second `β × α` in Zelevinsky's notation.
`IsIrreducible` is the Library notion (the lattice of subrepresentations is a
simple order, so the space is nonzero). The universes `uF` and `uV` are
independent; the conclusion is the existence of an isomorphism, with no
further structure.

The ranks are equal because the two products of blocks of ranks `k` and `l`
live on `GL_{k+l}` and `GL_{l+k}`, which are not syntactically the same group;
the equal-rank case is the one used by the adjacent reducibility proof.

## Provenance

This is a derived consequence of Zelevinsky 1980 (literature
`zelevinsky-1980-induced-ii`), Theorem 1.9, printed p.174 (PDF p.11): "if
`π₁ ∈ Alg G_n`, `π₂ ∈ Alg G_m` are of finite length then `π₁ × π₂` and
`π₂ × π₁` have the same composition factors". When `π₁ × π₂` is irreducible its
only composition factor is itself, so `π₂ × π₁`, which has the same
composition factors, is isomorphic to it. Zelevinsky's proof is via the
Gelfand–Kazhdan involution. The statement here restricts to irreducible
`α, β` (instead of finite length), equal ranks, and an irreducible product,
which is exactly what the proof of Zelevinsky 1980, Proposition 1.11, printed
p.175 (PDF p.12), uses to pass between `ρ × νρ` and `νρ × ρ`.

## Proposed proof route (not part of the statement)

Write `X = α × β` and `θ(g) = ᵗg⁻¹`. All representations involved are
admissible: irreducible smooth representations of `GL_n(F)` are admissible
(`Langlands.CuspidalSupport.cuspidalEmbedding`), and normalized induction
preserves admissibility. Then

1. `X^∨ ≅ X ∘ θ` (Gelfand–Kazhdan, `Langlands.gelfandKazhdanContragredient`,
   since `X` is irreducible);
2. `X ∘ θ ≅ (β ∘ θ) × (α ∘ θ)` (`Langlands.Parabolic.normalizedProductInverseTranspose`,
   after identifying the reversed block shape with `twoBlocks k k`);
3. `β ∘ θ ≅ β^∨` and `α ∘ θ ≅ α^∨` (Gelfand–Kazhdan);
4. `β^∨ × α^∨ ≅ (β × α)^∨` (`twistedProductOrdinaryDual` at exponents `0`,
   or the normalized induction duality);
5. hence `X^∨ ≅ (β × α)^∨`, and taking smooth duals again with admissible
   reflexivity gives `X ≅ β × α`.

This paragraph describes an intended proof, not an assumption.
