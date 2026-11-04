# Integral coroot generation for simply connected split groups from the classification

Worker 1537. This module is a derived, conditional assembly step toward
`SplitSimplyConnectedCorootSpanStatement` (module
`Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement`). It proves
that statement from three published propositions, which enter as hypotheses.
It proves none of those three. It is not a proof of
`SplitSimplyConnectedCorootSpanStatement` itself: that proof needs the three
inputs to be proved first.

## The inputs

`SplitSimplyConnectedCorootSpanInputsStatement.{u}` is the conjunction, at one
arbitrary universe `u`, of:

- `SplitReductiveExistenceStatement` (Existence Theorem, Milne Theorem
  23.55): every reduced root datum with finitely many roots on a finitely
  generated lattice is isomorphic to a root datum of a split maximal torus of
  a connected reductive group;
- `SplitCentralIsogenyExistenceStatement` (Isogeny Theorem, existence half,
  central case, Milne Theorem 23.9): a morphism of root data of split
  reductive groups with injective weight and coweight maps comes from a
  central isogeny `φ` and a torus homomorphism `t` with `iC ≫ φ = t ≫ i`, and
  the weight map is pullback of characters along `t`;
- `SplitSemisimpleRootDatumStatement` (Milne Proposition 21.48 and its dual
  form): a split connected reductive group is semisimple exactly when the
  roots, equivalently the coroots, span a subgroup of finite index.

The definition only bundles these statements, all in module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`. It adds no
hypothesis of its own.

## The theorem

`splitSimplyConnectedCorootSpan_of_inputs` states that
`SplitSimplyConnectedCorootSpanInputsStatement.{u}` implies
`SplitSimplyConnectedCorootSpanStatement.{u}`. The conclusion is that
statement exactly. For every field `k : Type u`, every algebraically simply
connected `G` over `Spec k`, every split maximal torus `i : T ⟶ G`, and every
reduced root datum `P` of `i` with a finite index type `J`, it gives
`P.corootSpan ℤ = ⊤`. This is integral generation of the cocharacter lattice
by the coroots, not only rational generation or finite index.

## The proof

The proof follows the converse half of Milne Proposition 23.59 (printed
p.502, PDF p.518): "suppose that X ≠ P(Φ). Then the inclusion X ↪ P(Φ) is a
nonisomorphic central isogeny (X, Φ, Φ^∨) → (P(Φ), Φ, Φ^∨). According to
Corollary 23.56, this arises from a nonisomorphic central isogeny
(G′, T′) → (G, T) and so G is not simply connected." The Lean proof runs this
argument directly rather than by contradiction. Steps 1 to 5 build the same
cover as the published proof of `splitSimplyConnectedCoverExistence_of_inputs`
(module `Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceAssembly`),
and the Lean code for them follows that proof. The steps:

1. `G` is semisimple, hence connected reductive
   (`hG.isSemisimple.isConnectedReductive`). The coroot half of
   `SplitSemisimpleRootDatumStatement` gives that
   `cocharacterLattice T ⧸ P.corootSpan ℤ` is finite.
2. `SimplyConnectedRootDatum.rootDatum P` is the simply connected root datum
   `(Hom(ℤΦ^∨, ℤ), Φ, ℤΦ^∨, Φ^∨)` (module
   `Langlands.LinearAlgebra.SimplyConnectedRootDatum`). It is reduced because
   `P` is, and its weight lattice is finitely generated; both instances are
   found by `inferInstance`. `SplitReductiveExistenceStatement` applied to it
   gives a connected reductive `C`, a split maximal torus `iC : TC ⟶ C`, a root
   datum `Q` of `iC` and an isomorphism of root pairings
   `e : rootDatum P ≃ Q`.
3. The morphism of root data is `f := e.toHom.comp (toRootDatum P) : P → Q`.
   `toRootDatum P` restricts characters to the coroot lattice and includes the
   coroot lattice into `Y = cocharacterLattice T`. Its weight map is injective
   because the coroots span a subgroup of finite index (step 1,
   `injective_toRootDatum_weightMap`). Its coweight map is the inclusion
   `(P.corootSpan ℤ).subtype` (`injective_toRootDatum_coweightMap`). Composing
   with the bijections of `e` keeps both maps injective.
4. `SplitCentralIsogenyExistenceStatement`, with source `(C, TC, iC, Q)`,
   target `(G, T, i, P)` and morphism `f`, gives a central isogeny
   `φ : C ⟶ G` and a torus map `t : TC ⟶ T` with `iC ≫ φ = t ≫ i` and
   `f.weightMap χ = t ≫ χ` for every character `χ` of `T`.
5. The coroots of `rootDatum P` span its whole coweight lattice
   (`corootSpan_rootDatum`). The same holds for `Q`, since `e` is an
   isomorphism (`corootSpan_eq_top_of_equiv`). So the quotient of the
   cocharacter lattice of `TC` by `Q.corootSpan ℤ` is the quotient by `⊤`,
   which is finite. The coroot half of `SplitSemisimpleRootDatumStatement`,
   applied to `C`, makes `C` semisimple.
6. `G` is simply connected and `φ` is a central isogeny from the semisimple
   group `C`, so `φ` is an isomorphism (`IsSimplyConnected.central_isogeny_isIso`).
7. The torus `TC` is maximal in `C`, and `T` is a torus with `i` a closed
   subgroup. Since `φ` is an isomorphism and `iC ≫ φ = t ≫ i`, the torus map
   `t` is an isomorphism (`IsMaximalTorus.isIso_factor_of_isIso`, module
   `Langlands.GroupScheme.Reductive.RootDatumHomLattices`).
8. Both `P` and `Q` have the actual lattice pairings (first component of
   `IsRootDatumOf`), and the weight map of `f` is pullback along the
   isomorphism `t`. So the coweight map of `f` is postcomposition with `t` and
   is surjective (`RootDatumHom.surjective_coweightMap_of_isIso`).
9. The coweight map of `f` is the coweight map of `e` followed by the
   inclusion `(P.corootSpan ℤ).subtype`. Every `y` in `Y` is the image of
   some `z`, so `y` is the inclusion of `e.toHom.coweightMap z`. The inclusion
   is therefore surjective, and its range, which is `P.corootSpan ℤ`
   (`Submodule.range_subtype`), is `⊤` (`LinearMap.range_eq_top`).

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The route is the converse half of Milne Proposition 23.59. Milne writes the
condition as `X = P(Φ)` with `P(Φ)` a lattice in `X ⊗ ℚ`, and he gets the
nonisomorphic central isogeny from Corollary 23.56 of the Existence and
Isogeny Theorems. Here the weight lattice of the simply connected root datum
is the dual of the coroot lattice. For semisimple root data the two agree by
Milne C.26 (printed p.613, PDF p.629), as the Markdown of
`Langlands.LinearAlgebra.SimplyConnectedRootDatum` explains. The conclusion
is in the equivalent coroot form `P.corootSpan ℤ = ⊤`, as stated in
`SplitSimplyConnectedCorootSpanStatement`. The Library's
`SplitCentralIsogenyExistenceStatement` supplies the central isogeny together
with its torus map, so the proof shows directly that the torus map, and hence
the coweight map, is an isomorphism. It does not reason by contradiction. The
input bundle is an internal packaging of the published statements this route
uses, following the Library pattern of
`SplitSimplyConnectedCoverInputsStatement`. Source: J. S. Milne, *Algebraic
Groups* (2017), source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
