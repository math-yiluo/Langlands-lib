# Normalizing the evaluations of a projective frame

This module turns a projective frame of torsion evaluations into an explicit
product decomposition of the cubic direct image. It has two parts: a general
statement about families of morphisms in a category, and its application to a
datum whose projective frame locus is the whole base. All schemes lie in one
arbitrary universe `u`.

## The general construction (namespace `FrameNormalization`)

Let `C` be a category with zero morphisms and finite products, `I` a finite
type with decidable equality, and `f i : M ⟶ L i` a family of morphisms out of
one object `M`.

- `omission f k : M ⟶ ∏ᶜ (j ≠ k) L j` is the joint morphism to the product
  over all indices other than `k`. `omission_π` gives its components.

For the rest of the namespace, assume that every `omission f k` is an
isomorphism (instance argument `∀ k, IsIso (omission f k)`).

- `slot f k i : L i ⟶ M`, for `i ≠ k`, is the inclusion of the `i`-th factor of
  the product followed by the inverse of `omission f k`. By `slot_eval` and
  `slot_eval'`, `slot f k i ≫ f j` is the `(i, j)` entry
  `Pi.ι _ i ≫ Pi.π _ j` of the product. This entry is the identity for
  `j = i` and zero for every other `j ≠ k`.
- `hom_ext_omit`: two morphisms into `M` agree when their composites with
  every `f j`, `j ≠ k`, agree.
- `lastComponent f k i : L i ≅ L k`, for `i ≠ k`. Its morphism is
  `slot f k i ≫ f k` and its inverse is `slot f i k ≫ f i`. Both composites
  are checked with `hom_ext_omit`, once for the omitted index `i` and once for
  the omitted index `k`.
- `normalizedFrame f k : (∏ᶜ (j ≠ k) L k) ≅ M` is the composite of the
  product of the inverses of the `lastComponent f k i` with the inverse of
  `omission f k`. By `ι_normalizedFrame`, its `i`-th inclusion is
  `(lastComponent f k i).inv ≫ slot f k i`.
- `normalizedFrame_offDiag`: the `i`-th inclusion followed by `f j` is zero
  for `i ≠ j`, both different from `k`.
- `normalizedFrame_omitted`: the `i`-th inclusion followed by `f k` is the
  identity of `L k`.
- `normalizedFrame_diag` and `isIso_normalizedFrame_diag`: the `i`-th
  inclusion followed by `f i` equals `(lastComponent f k i).inv`, so it is an
  isomorphism.

## Application to the frame locus

Fix `P : Prerequisites`, a scheme `S`, natural numbers `g d n m`, a datum
`a : Datum P S g d n` and a family `ρ : Fin (m + 2) → Fin (2 * g) → ZMod n`.

- `Datum.isIso_frameEvaluation_of_frameLocus_eq_top`: if
  `a.frameLocus ρ = ⊤`, then every omission evaluation
  `a.frameEvaluation ρ k` is an isomorphism of module sheaves on `S`. The proof
  uses the published `mem_sSup_isIso_restrict_iff` and
  `isIso_iff_forall_mem_isoLocus`. Every point of `S` has an open neighbourhood
  on which all the restricted evaluations are isomorphisms. So every point lies
  in each stalk-isomorphism locus. No local freeness of the cubic direct image
  is used.
- `Datum.exists_normalizedFrame`: if `a.frameLocus ρ = ⊤`, there is an
  isomorphism `e` from the product of `m + 1` copies of the line
  `t_last^* L³` to `a.rigidificationModule`. Here `t_last` is the torsion
  section `a.torsionPoint (ρ (Fin.last (m + 1)))`, `L³` is `a.cubicBundle`,
  and the copies are indexed by the entries `j ≠ Fin.last (m + 1)`. With
  `τ_i = Pi.ι _ i ≫ e.hom`:
  1. `τ_i ≫ a.torsionEvaluation (ρ j) = 0` for `i ≠ j`;
  2. `τ_i ≫ a.torsionEvaluation (ρ (Fin.last (m + 1))) = 𝟙`;
  3. `τ_i ≫ a.torsionEvaluation (ρ i)` is an isomorphism.

  This is the general construction with `f i = a.torsionEvaluation (ρ i)` and
  `k = Fin.last (m + 1)`, since `a.frameEvaluation ρ k` is by definition
  `omission f k`.

## Provenance

This is the frame `M ≅ Λ^{m+1}`, with `Λ = t_last^* L³`, described in the
Markdown of `FrameEmbeddingExistenceStatement`. It is the linear rigidification
used by Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
§7.2, printed p.131 (PDF p.144 of registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
There the embedding of a polarized abelian scheme is determined by a
trivialization of the projective bundle of `π_* L³`. Normalizing by the
evaluations at the torsion frame and the categorical argument above are
derived here: they are not in the source.
