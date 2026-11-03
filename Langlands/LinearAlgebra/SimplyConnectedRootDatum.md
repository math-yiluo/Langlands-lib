# The simply connected root datum of a root datum

Module `Langlands.LinearAlgebra.SimplyConnectedRootDatum`. Author: Worker 1391.

This module is a helper for proof task `a41119fb-a633-4b81-a979-4b08e9ddbb15`, which proves
`SimplyConnectedCoverExistenceStatement`. That proof follows Milne, *Algebraic Groups* (2017),
Remark 23.60: for a split semisimple group with root datum `(X, Φ, Φ^∨)`, the universal covering
is the central isogeny that corresponds to the isogeny of root data
`(X, Φ, Φ^∨) → (P(Φ), Φ, Φ^∨)`. This module builds the target root datum `(P(Φ), Φ, Φ^∨)` and
that morphism for Mathlib root data.

Everything here is pure linear algebra about Mathlib's `RootDatum ι X Y`: a perfect pairing
`P.toLinearMap : X → Y → ℤ`, roots `P.root : ι ↪ X`, coroots `P.coroot : ι ↪ Y` and the
permutations `P.reflectionPerm`. The module states nothing about group schemes.

## Construction

Let `P : RootDatum ι X Y` have finitely many roots (`Finite ι`). Write
`L = P.corootSpan ℤ`, the subgroup of `Y` spanned by the coroots (Milne's `Q(R^∨)`). The weight
lattice of the new datum is `Dual ℤ L = Hom(L, ℤ)`.

- `weightMap P : X →ₗ[ℤ] Dual ℤ L` restricts a character to the coroot lattice:
  `weightMap P x y = P.toLinearMap x y` for `y ∈ L`.
- `root P i = weightMap P (P.root i)`. The theorem `root_injective` shows that these restricted
  roots are pairwise distinct. If `root P i = root P j`, then `P.pairing i j = 2` and
  `P.pairing j i = 2`, so `i = j` by Mathlib's `RootPairing.pairing_two_two_iff`.
- `rootDatum P : RootDatum ι (Dual ℤ L) L` is the main definition. Its pairing is the evaluation
  pairing `LinearMap.id : Dual ℤ L → L → ℤ`, which is perfect because `L` is a reflexive
  `ℤ`-module (`isReflexive_corootSpan`: `L` is a finitely generated subgroup of the reflexive
  module `Y`). Its roots are `root P i`, its coroots are `P.corootSpanMem ℤ i` (the coroot
  `P.coroot i` as an element of `L`), and its reflection permutations are those of `P`. The
  root-datum axioms reduce to the corresponding axioms of `P`: every pairing of the new datum
  equals the pairing of `P` (`rootDatum_pairing`).
- `toRootDatum P : RootPairing.Hom P (rootDatum P)` is the morphism of root pairings with
  weight map `weightMap P`, coweight map the inclusion `L → Y`, and the identity on the index
  set `ι`.

The `@[simp]` lemmas `rootDatum_toLinearMap`, `rootDatum_root`, `rootDatum_coroot`,
`rootDatum_reflectionPerm`, `toRootDatum_weightMap`, `toRootDatum_coweightMap` and
`toRootDatum_indexEquiv` record these definitions. The instance `finite_dual_corootSpan` says that
`Dual ℤ L` is a finitely generated `ℤ`-module. This holds because `L` is finitely generated and
torsion-free, hence free.

## Properties

- `corootSpan_rootDatum`: the coroots of `rootDatum P` span all of its coweight lattice `L`. In
  Milne's terms, the cocharacter lattice of the new datum is the coroot lattice `Q(Φ^∨)`. This is
  the property used by the simply-connectedness criterion (Milne, Proposition 23.29).
- `injective_toRootDatum_coweightMap`: the coweight map `L → Y` is injective.
- `injective_toRootDatum_weightMap`: if `Y ⧸ L` is finite, then the weight map `X → Dual ℤ L` is
  injective. Proof: if `x` vanishes on `L`, then for each `y ∈ Y` some `n > 0` has `n • y ∈ L`
  (the additive order of the class of `y` in the finite group `Y ⧸ L`), so `n * ⟨x, y⟩ = 0` and
  `⟨x, y⟩ = 0`. Hence `P.toLinearMap x = 0`, and `x = 0` because the pairing is perfect.
- `isReduced_rootDatum`: if `P` is reduced, so is `rootDatum P`. The two data have the same
  pairings, hence the same Coxeter weights. Mathlib's
  `RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent` therefore transfers linear
  dependence of two roots from `rootDatum P` to `P`. Reducedness of `P` gives
  `P.root i = ± P.root j`, and the linear map `weightMap P` carries this to the restricted roots.
- `corootSpan_eq_top_of_equiv`: if `e : RootPairing.Equiv P Q` and the coroots of `P` span its
  coweight lattice, then the coroots of `Q` span the coweight lattice of `Q`. Proof: the bijective
  coweight map of `e` carries the coroot span of `Q` onto the coroot span of `P`.

Together these provide the root-datum input of the split case of Remark 23.60. Take a reduced
root datum `P` of a split semisimple group, so that `Y ⧸ L` is finite (Milne, Proposition 21.48
with Definition C.34, in dual form). Then `rootDatum P` is reduced, and `toRootDatum P` has
injective weight and coweight maps. So it is a central isogeny of root data in the sense used by
the Isogeny Theorem (Milne, Theorem 23.9 with Definitions 23.1 and 23.2). A group realizing
`rootDatum P`, or any root datum equivalent to it, has coroots that span its cocharacter lattice.

## Sources and provenance

Milne, *Algebraic Groups* (2017), source id `milne-2017-algebraic-groups`; printed page = PDF
page − 16.

- C.26, printed p. 613 (PDF p. 629): for a root system `(V, R)` over `ℚ`, the weight lattice is
  `P(R) = {v ∈ V | ⟨v, α^∨⟩ ∈ ℤ for all α ∈ R}`, and "P(R) is the unique lattice in V such that
  ⟨ , ⟩ restricts to a perfect pairing P(R) × Q(R^∨) → ℤ".
- C.35, printed p. 615 (PDF p. 631): for a semisimple root datum `(X, R)`,
  `Q(R) ⊂ X ⊂ P(R)`.
- Proposition 23.59, printed p. 502 (PDF p. 518): for split semisimple `(G, T)` with diagram
  `(V, Φ, X)`, "the inclusion X ↪ P(Φ) is a nonisomorphic central isogeny
  (X, Φ, Φ^∨) → (P(Φ), Φ, Φ^∨)" when `X ≠ P(Φ)`. `G` is simply connected exactly when
  `X = P(Φ)`.
- Remark 23.60, printed p. 502 (PDF p. 518): "For a split group (G, T), the universal covering is
  the central isogeny corresponding to the isogeny of root data (X, Φ, Φ^∨) → (P(Φ), Φ, Φ^∨)."

Provenance: derived. Milne defines `P(Φ)` inside the rational span `V` of the roots. This module
realizes it intrinsically as `Hom(Q(Φ^∨), ℤ)`, the lattice in perfect duality with the coroot
lattice. By C.26 the two agree for semisimple data. The morphism `toRootDatum P` is the
restriction `X → Hom(Q(Φ^∨), ℤ)`. For a semisimple datum this is Milne's inclusion
`X ↪ P(Φ)` under that identification. The construction makes sense for every root datum with
finitely many roots. For a non-semisimple datum it produces the simply connected datum of the
semisimple part, and `toRootDatum P` then has a non-injective weight map. The injectivity lemma
therefore assumes that `Y ⧸ L` is finite. The proofs are Worker 1391's and are internal to this
module, except for the Mathlib lemmas named above.
