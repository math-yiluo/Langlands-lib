# Reduction of Milne 17.84 to the algebraically closed case and Milne 17.82

Worker 1391. This module states the algebraically closed case of Milne
Proposition 17.61(a) as a new proposition,
`AlgClosedMaximalTorusCentralizerStatement`. It then proves that this case and
the forward implication of Milne Theorem 17.82 together imply the published
proposition `MaximalTorusCentralizerStatement` (module
`Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement`, Milne
Corollary 17.84). That proposition says that a maximal torus of a connected
reductive group over a field is its own centralizer.

The module proves neither `AlgClosedMaximalTorusCentralizerStatement` nor
`MaximalTorusCentralizerStatement`. Both inputs of the reduction remain open in
the Library:

- the forward implication of 17.82, `MaximalTorusBaseChangeForwardStatement`,
  which the Library reduces to its central case
  `CentralMaximalTorusBaseChangeStatement`;
- `AlgClosedMaximalTorusCentralizerStatement`, which Milne proves with Borel
  subgroups (17.38, 17.39, 17.56).

## The new proposition

`AlgClosedMaximalTorusCentralizerStatement.{u}` says: for every algebraically
closed field `k : Type u`, every group scheme `G` over `Spec k` with
`IsConnectedReductive G`, every commutative group scheme `T` over `Spec k` and
every `j : T ⟶ G` with `IsMaximalTorus j`,

```lean
torusCentralizer j = SubgroupFunctor.range j
```

This is the body of the published `MaximalTorusCentralizerStatement` with the
extra hypothesis `[IsAlgClosed k]`, and nothing else changed. The equality is
of subgroup functors of `G` on every test scheme over `Spec k`, nonaffine and
nonreduced ones included. `torusCentralizer j` (module
`Langlands.GroupScheme.Rational.TorusCentralizer`) consists of the points of
`G` that commute with all points of `T` after every refinement of the test
scheme. `SubgroupFunctor.range j` consists of the points that factor through
`j`. `IsMaximalTorus j` (module `Langlands.GroupScheme.Torus.Maximal`) says
that `j` is a closed torus of `G` that is maximal among closed tori of `G`
over `k`.

The declaration is a `def` of type `Prop`.

## Main results

- `torusCentralizer_eq_range_of_baseChange`: let `k ⊆ K` be fields, `G` a
  group scheme over `Spec k`, `T` a commutative group scheme over `Spec k`
  whose structure morphism is affine, and `j : T ⟶ G` a closed subgroup
  (`IsClosedSubgroup j`). If the centralizer of `j_K : T_K ⟶ G_K` equals
  the range of `j_K`, then `torusCentralizer j = SubgroupFunctor.range j`.
  This needs no hypothesis on `G` and no reductivity.
- `MaximalTorusCentralizerReductionStatement.{u}`: the proposition
  `MaximalTorusBaseChangeForwardStatement.{u} →
  AlgClosedMaximalTorusCentralizerStatement.{u} →
  MaximalTorusCentralizerStatement.{u}`. It is a `def` of type `Prop`.
- `maximalTorusCentralizerReduction`: a proof of
  `MaximalTorusCentralizerReductionStatement.{u}`.
- `maximalTorusCentralizer_of_centralMaximalTorusBaseChange`:
  `CentralMaximalTorusBaseChangeStatement.{u} →
  AlgClosedMaximalTorusCentralizerStatement.{u} →
  MaximalTorusCentralizerStatement.{u}`.

All results use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The universe `u` is arbitrary. Every field `k` is allowed, in
every characteristic, finite and imperfect fields included.

## Proof of `torusCentralizer_eq_range_of_baseChange`

Write `b : Spec K ⟶ Spec k` for the morphism induced by `algebraMap k K`, and
a subscript `K` for base change along `b`.

1. **A representative of the centralizer.** The Library theorem
   `fieldCentralizerRepresentability` (module
   `Langlands.GroupScheme.FieldCentralizerRepresentabilityProof`) gives a
   group scheme `C` and a homomorphism `c : C ⟶ G` that represents
   `torusCentralizer j`. Because `range j ≤ torusCentralizer j`, the map `j`
   factors as `t ≫ c`, where `t = torusCentralizerFactor j hc` (module
   `Langlands.GroupScheme.Rational.TorusCentralizerFactorization`).
2. **After base change.** `SubgroupFunctor.IsRepresentedBy.baseChange`
   (module `Langlands.GroupScheme.SubgroupBaseChange`) shows that `c_K`
   represents the base change of `torusCentralizer j`. By
   `torusCentralizer_baseChange` (module
   `Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction`), that
   base change is the centralizer of `j_K`, which is `range j_K` by
   hypothesis. The map `j_K` is a closed immersion
   (`IsClosedSubgroup.baseChange`), hence a monomorphism, so it also
   represents `range j_K`.
3. **`t_K` is an isomorphism.** Two representatives of the same subgroup
   functor are related by the isomorphism `isoOfIsRepresentedBy`. Both `t_K`
   and the forward map of this isomorphism, composed with `c_K`, give `j_K`.
   Since `c_K` is a representative, it cancels on the right
   (`IsRepresentedBy.hom_ext`). So `t_K` is that isomorphism.
4. **Descent.** The morphism `b` is flat and surjective, because a field
   extension is faithfully flat (`RingHom.faithfullyFlat_algebraMap_iff` and
   Mathlib's `flat_and_surjective_SpecMap_iff`). The Library theorem
   `isIso_of_baseChange` (module `Langlands.GroupScheme.BaseChangeReflection`)
   then shows that `t` is an isomorphism.
5. **Conclusion.** `torusCentralizer j = range c` (from `hc`), and
   `range c = range (t ≫ c) = range j` because `t` is an isomorphism
   (`SubgroupFunctor.range_iso_comp`).

## Proof of `maximalTorusCentralizerReduction`

Fix `k`, a connected reductive `G` and a maximal torus `j : T ⟶ G`, and let
`k̄ = AlgebraicClosure k`.

1. `G` is smooth with affine structure morphism, since it is connected
   reductive. `T` has affine structure morphism, since `j` is a closed
   subgroup of the affine `G` (`IsClosedSubgroup.isAffineHom`).
2. The forward implication of 17.82 makes `j_k̄` a maximal torus of `G_k̄`.
3. `IsConnectedReductive.baseChange_toAlgebraicClosure` (module
   `Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange`, a proved
   Library result) makes `G_k̄` connected reductive.
4. The algebraically closed case then gives
   `torusCentralizer j_k̄ = range j_k̄`. `torusCentralizer_eq_range_of_baseChange`
   with `K = k̄` gives `torusCentralizer j = range j`.

## Proof of `maximalTorusCentralizer_of_centralMaximalTorusBaseChange`

The Library proves `maximalTorusBaseChangeForwardReduction`:
`TorusCentralizerSmoothStatement → CentralMaximalTorusBaseChangeStatement →
MaximalTorusBaseChangeForwardStatement` (module
`Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction`). It also
proves `torusCentralizerSmooth : TorusCentralizerSmoothStatement` (module
`Langlands.GroupScheme.Torus.CentralizerSmoothProof`). These two give the
forward implication of 17.82 from its central case, and
`maximalTorusCentralizerReduction` finishes the proof.

## Provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Proposition 17.61 (printed p.372, PDF p.388): "Let G be a reductive group.
  (a) Let T be a torus in G such that T_{k^a} is maximal in G_{k^a}. Then
  C_G(T) = T." Its proof begins: "(a) We may suppose that k is algebraically
  closed. Every Borel subgroup containing T contains C_G(T) (see 17.39), and
  C_G(T) is smooth and connected (13.10, 17.38)". It then applies 17.56.
  `AlgClosedMaximalTorusCentralizerStatement` is the case of 17.61(a) to which
  this proof reduces. Over an algebraically closed `k` we have `k^a = k`, so
  the hypothesis "T_{k^a} is maximal in G_{k^a}" says only that `T` is
  maximal in `G`. As in the published `MaximalTorusCentralizerStatement`,
  Milne's reductive group is the Library's `IsConnectedReductive`, and
  `C_G(T) = T` is the equality of subgroup functors `torusCentralizer j =
  range j`.
- Theorem 17.82 (printed p.379, PDF p.395): "Let G be a group variety over k
  and let k' be a field containing k. A torus T in G is maximal if and only if
  T_{k'} is maximal in G_{k'}." Its forward implication is the Library's
  `MaximalTorusBaseChangeForwardStatement`.
- Corollary 17.84 (printed p.379, PDF p.395): "A torus T in a reductive group
  G is maximal if and only if C_G(T) = T. PROOF. If T is maximal in G, then
  T_{k^a} is maximal in G_{k^a}, and so C_{G_{k^a}}(T_{k^a}) = T_{k^a} by
  Proposition 17.61. But the formation of centralizers commutes with extension
  of the base field, and so this implies that C_G(T) = T. The converse is
  obvious."

`MaximalTorusCentralizerReductionStatement` is internal: it records the
"only if" half of Milne's proof of 17.84 as an implication between Library
propositions. The Lean proof follows that route, with `k^a` taken to be
Mathlib's `AlgebraicClosure k`. Milne's "the formation of centralizers commutes
with extension of the base field" appears in two steps:
`torusCentralizer_baseChange` (a Library result), and the faithfully flat
descent of the isomorphism `t` in `torusCentralizer_eq_range_of_baseChange`.
That descent argument is Worker 1391's, and so are the Lean proofs.
