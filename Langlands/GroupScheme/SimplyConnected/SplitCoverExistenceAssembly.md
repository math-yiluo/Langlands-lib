# Simply connected central covers of split semisimple groups from the classification

Worker 1391. This module is a derived, conditional assembly step toward
`SplitSimplyConnectedCoverExistenceStatement` (module
`Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement`). It
proves that statement from five published propositions, which enter as
hypotheses. It proves none of those five, and it does not touch the descent
from a splitting field to `k` or the factorization law of the full
`SimplyConnectedCoverExistenceStatement`.

## The inputs

`SplitSimplyConnectedCoverInputsStatement.{u}` is the conjunction, at one
arbitrary universe `u`, of:

- `RootDatumExistenceStatement` (Milne Theorem 21.11 and Corollary 21.12):
  a split maximal torus of a connected reductive group has a reduced root
  datum, indexed by a finite type;
- `SplitReductiveExistenceStatement` (Existence Theorem, Milne Theorem
  23.55): every reduced root datum with finitely many roots on a finitely
  generated lattice is isomorphic to a root datum of a split maximal torus of
  a connected reductive group;
- `SplitCentralIsogenyExistenceStatement` (Isogeny Theorem, existence half,
  central case, Milne Theorem 23.9): a morphism of root data of split
  reductive groups with injective weight and coweight maps comes from a
  central isogeny;
- `SplitSemisimpleRootDatumStatement` (Milne Proposition 21.48 and its dual
  form): a split connected reductive group is semisimple exactly when the
  roots, equivalently the coroots, span a subgroup of finite index;
- `SplitCorootSpanSimplyConnectedStatement` (sufficiency half of the coroot
  criterion, Milne Proposition 23.29): a split semisimple group whose coroots
  span the whole cocharacter lattice is simply connected.

The definition only bundles these statements. It adds no hypothesis of its own.

## The theorem

`splitSimplyConnectedCoverExistence_of_inputs` states that
`SplitSimplyConnectedCoverInputsStatement.{u}` implies
`SplitSimplyConnectedCoverExistenceStatement.{u}`. The conclusion is that
statement exactly: for every field `k : Type u`, every semisimple `G` over
`Spec k` and every split maximal torus `i : T ⟶ G`, there are an actual group
scheme `C` over `Spec k` and an actual homomorphism `π : C ⟶ G` with
`IsSimplyConnected C` and `IsCentralIsogeny π`.

## The proof

The proof follows Milne Remark 23.60 (printed p.502, PDF p.518): "For a split
group (G,T), the universal covering is the central isogeny corresponding to the
isogeny of root data (X,Φ,Φ^∨) → (P(Φ),Φ,Φ^∨)." The steps in the Lean proof:

1. `G` is connected reductive (`IsSemisimple.isConnectedReductive`).
   `RootDatumExistenceStatement` gives a finite index type `J` and a reduced
   root datum `P` of `i` on the actual lattices `X = characterLattice T` and
   `Y = cocharacterLattice T`.
2. Since `G` is semisimple, the coroot half of
   `SplitSemisimpleRootDatumStatement` gives that `Y ⧸ P.corootSpan ℤ` is
   finite.
3. `SimplyConnectedRootDatum.rootDatum P` is the simply connected root datum
   `(Hom(ℤΦ^∨, ℤ), Φ, ℤΦ^∨, Φ^∨)` (module
   `Langlands.LinearAlgebra.SimplyConnectedRootDatum`). It is reduced
   (`isReduced_rootDatum`), and its weight lattice is finitely generated
   (`finite_dual_corootSpan`). `SplitReductiveExistenceStatement` applied to it
   gives a connected reductive `C`, a split maximal torus `iC : TC ⟶ C`, a root
   datum `Q` of `iC` and an isomorphism of root pairings
   `e : rootDatum P ≃ Q`.
4. The morphism of root data is `f := e.toHom.comp (toRootDatum P) : P → Q`.
   `toRootDatum P` restricts characters to the coroot lattice and includes the
   coroot lattice into `Y`. Its weight map is injective because the coroots
   span a subgroup of finite index (step 2,
   `injective_toRootDatum_weightMap`). Its coweight map is an inclusion
   (`injective_toRootDatum_coweightMap`). Composing with the bijections of
   `e` keeps both maps injective.
5. `SplitCentralIsogenyExistenceStatement`, with source `(C, TC, iC, Q)`,
   target `(G, T, i, P)` and morphism `f`, gives a central isogeny
   `π : C ⟶ G`. The torus map and the compatibility conditions that the
   statement also provides are not needed and are discarded.
6. The coroots of `rootDatum P` span its whole coweight lattice
   (`corootSpan_rootDatum`). The same holds for `Q`, since `e` is an
   isomorphism (`corootSpan_eq_top_of_equiv`). So the quotient of the
   cocharacter lattice of `TC` by `Q.corootSpan ℤ` is the quotient by `⊤`,
   which is finite. The coroot half of `SplitSemisimpleRootDatumStatement`,
   applied to `C`, makes `C` semisimple.
7. `SplitCorootSpanSimplyConnectedStatement`, applied to `C`, `iC` and `Q`,
   makes `C` simply connected.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The route is Milne's Remark 23.60. Milne realizes `P(Φ)` as a lattice in
`X ⊗ ℚ`. Here the weight lattice of the simply connected root datum is the
dual of the coroot lattice. For semisimple root data the two agree by Milne
C.26 (printed p.613, PDF p.629), as the Markdown of
`Langlands.LinearAlgebra.SimplyConnectedRootDatum` explains. Milne gets simple
connectedness from Proposition 23.29 (`X = P(Φ)`). The Library's sufficiency
statement uses the equivalent coroot form `Q.corootSpan ℤ = ⊤` (see the
Markdown of `SplitCriterionStatement`). Source: J. S. Milne, *Algebraic
Groups* (2017), source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The
errata snapshot of 2026-11-02 (`milne-2017-algebraic-groups-errata-2026-11-02`)
has no entry for Remark 23.60.
