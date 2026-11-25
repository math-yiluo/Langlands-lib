# Homomorphisms with commutative image from a semisimple Weil restriction are trivial

Namespace `Langlands.GroupScheme.WeilAbelianImage`. This internal module assembles the proof of
`WeilAbelianImageTrivialityStatement`, in the general form `app_eq_one`. The exact
target is derived from it in `WeilAbelianImageTrivialityProof`.

## Contents

`B` is a finite, projective, étale `A`-algebra.

- `exists_split_cover' p`: the result `exists_split_cover` of module
  `Langlands.Algebra.FiniteEtaleSplitCover`, with the algebra `P` as an object of `CommAlgCat` and
  flatness and finite presentation stated for the ring map `algebraMap A P`.

Let `G'` be an affine group scheme of finite type over `Spec B`, `M` a group scheme over `Spec A`,
`T` an `A`-algebra and `c` a homomorphism of group functors on `T`-algebras from
`H = AffineWeil.groupScheme A B G'` to `M` whose values commute (`hc`). Assume `G'` is reductive
(`hred`) with semisimple geometric fibres (`hss`).

- `coverUnder X P` (abbreviation): `X ⊗[A] P` as a `T`-algebra, through `X → X ⊗[A] P`.
- `app_coverUnder_eq_one`: if `σ : P ⊗[A] B ≃ₐ[P] (Fin n → P)` is a splitting, then `c` is trivial
  over `X ⊗[A] P`. The graph idempotent family of `σ` (`exists_graph_family`) is pushed forward
  along `P → X ⊗[A] P` (`IsGraphIdempotent.map`), and `app_eq_one_of_split` (module
  `WeilAbelianImageSplit`) applies.
- `app_eq_one`: **`c` is trivial**: `c.app X x = 1` for every `T`-algebra `X` and every point `x` of
  `H` over `X`. For each prime `p` of `A` choose a splitting algebra `Q p` by `exists_split_cover'`.
  These form an fppf cover of `Spec A`. For each `p`, naturality of `c` along `X → X ⊗[A] Q p` and
  `app_coverUnder_eq_one` show that the image of `c.app X x` over `X ⊗[A] Q p` is `1`. By
  `affinePoint_eq_of_cover` (module `WeilAbelianImageCover`), `c.app X x = 1`.

## Proof outline of the whole argument

1. Base case `B = A` (module `AffineCommutatorTriviality`): every point of a reductive group with
   semisimple geometric fibres lies, on each member of some fppf cover of its test scheme, in the
   abstract commutator subgroup of the group of points there, i.e. it is locally a finite product
   of commutators (`RelativeDerived.LocallyCommutator`, supplied by
   `relativeSemisimpleFppfPerfect`). A homomorphism whose values commute kills that whole
   subgroup, and fppf separation of the points of `M` then gives the identity on the original
   test algebra.
2. The diagonal factor (module `WeilAbelianImageTransfer`): `c ∘ embNat` is a homomorphism from
   `G'` on `(B ⊗[A] T)`-algebras with commuting values, hence trivial by step 1 over `Spec B`.
3. Split case (module `WeilAbelianImageSplit`): if `B ⊗[A] X` splits, a point is the product of its
   components at the graph idempotents, each of which is a diagonal-factor point after a change of
   `B ⊗[A] T`-structure, and is killed by step 2.
4. General case (this module): `B` splits over an fppf cover of `Spec A`
   (`Langlands.Algebra.FiniteEtaleSplitCover`), and points of `M` are separated by that cover.

## Provenance

The statement is the derived statement `WeilAbelianImageTrivialityStatement`; see its
Markdown for the source (Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and
Theorem 5.3.1, registered as `conrad-2014-reductive-group-schemes`). The argument follows the
outline given there: every point of a semisimple group lies fppf-locally in the abstract
commutator subgroup (Conrad's Theorem 5.3.1, pp.160–163, uses fppf sheafification of that
subgroup), splitting of `B ⊗_A X`, and fppf separation of the points of `M`. The organisation is internal.
