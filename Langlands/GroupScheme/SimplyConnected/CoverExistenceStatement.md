# Statement: existence of simply connected central covers over arbitrary fields

Author: Worker 770.

This module states that every semisimple group scheme over an arbitrary field
has an actual simply connected central cover, with that cover's
unique-factorization law. It defines one proposition and proves nothing. The
declaration is a `Prop`-valued `def` in the namespace `Langlands.GroupScheme`,
with one universe parameter `u`.

## Lean statement

```lean
def SimplyConnectedCoverExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G), IsSimplyConnectedCover π
```

The module imports only `Langlands.GroupScheme.SimplyConnected.Basic`. It
reuses the Library declarations `GroupScheme`, `IsSemisimple` and
`IsSimplyConnectedCover` by name and introduces no new definition besides the
proposition.

## Quantifiers

- `k : Type u` is an arbitrary field in an arbitrary universe `u`. There is no
  perfectness, separable-closedness or characteristic hypothesis, so imperfect
  fields of positive characteristic are included.
- `G` is an arbitrary actual group scheme over `Spec k`, that is, a group
  object of `Over (Spec k)` (`GroupScheme S = Grp (Over S)`). Nothing about `G`
  is fixed in advance. There is no chosen maximal torus, root datum, pinning or
  split form, and no assumption that `G` is split.
- The only hypothesis is `IsSemisimple G`, stated as an explicit implication.
- The conclusion is existential in both the covering group `C` (an actual group
  scheme over `Spec k`) and the actual homomorphism `π : C ⟶ G` of group
  schemes over `Spec k`. The map is part of the witness, so the statement
  supplies a covering morphism, not only a group. No cover, factorization law,
  lifting property or base-change property is assumed as data. All of them
  belong to what a proof must construct.

## Scheme-level meaning

`IsSemisimple G` (module `GroupScheme.Reductive.Semisimple`) has two fields.
`IsConnectedReductive G` asks that the structure morphism of `G` be smooth and
affine, that the underlying space be connected, and that the base change of `G`
to an algebraic closure of `k` have trivial unipotent radical. `HasFiniteCenter
G` asks that the full scheme-theoretic centre be represented by an actual closed
subgroup that is finite over `k`. The centre is the all-test subgroup functor:
a point over a test scheme `T` is central when every restriction of it
commutes with every point over every `T' → T`. Nonreduced test schemes are
included, and the centre may be nonsmooth or disconnected.

`IsSimplyConnectedCover π` (module `GroupScheme.SimplyConnected.Basic`) has
four fields.

1. `isSemisimple : IsSemisimple G` repeats the hypothesis.
2. `isSimplyConnected : IsSimplyConnected C`: `C` is semisimple, and every
   central isogeny `H ⟶ C` from a semisimple group scheme `H` over `Spec k` is
   an isomorphism. This is algebraic simple connectedness, with no topological
   condition.
3. `isCentralIsogeny : IsCentralIsogeny π`: the scheme morphism underlying `π`
   is finite, flat, surjective and locally of finite presentation, and the
   inclusion of the actual pullback kernel of `π` is central. Equivalently, on
   every test scheme `T`, including nonreduced ones, every `T`-point of `C`
   killed by `π` lies in the full centre of `C`. The kernel keeps its possible
   nonreduced structure; for example `μ_p` in characteristic `p` is allowed.
4. `universal : HasCentralCoverUniversalProperty π`: for every semisimple group
   scheme `H` over `Spec k` and every central isogeny `q : H ⟶ G`, there is a
   unique homomorphism `a : C ⟶ H` with `a ≫ q = π`. Lean's `a ≫ q` is the
   composite "first `a`, then `q`", that is, `q ∘ a = π`.

So the conclusion has a semisimple target, a simply connected source, a finite
flat surjective locally finitely presented covering morphism with full central
kernel, and its explicit unique-factorization law.

Uniqueness is not part of this proposition, because the Library already derives
it from the conclusion. Given two witnesses `π : C ⟶ G` and `π' : C' ⟶ G`, the
published `IsSimplyConnectedCover.iso` gives an isomorphism `C ≅ C'`.
`IsSimplyConnectedCover.iso_hom_comp` shows that it commutes with the covering
maps, and `IsSimplyConnectedCover.iso_unique` shows that it is the only such
isomorphism. These declarations are cited here and not redefined.

## Sources and provenance

Provenance: derived. Below, "derived" means that the conclusion combines the
existence assertion of one source with the universal property in a second
source, and the packaging is this Library's.

Sources:

- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
  edition (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`,
  SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
- Milne's official errata for that book, HTML snapshot of 2026-11-02, source
  `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.

### Existence: CGP, Corollary A.4.11(1)

The paragraph before CGP Corollary A.4.11 (printed p. 500, PDF p. 526)
reads: "Recall that a connected semisimple group G over a field k is called
simply connected if it admits no nontrivial central cover (i.e., any central
k-isogeny G′ → G from a connected semisimple k-group is an isomorphism)." The
Library's `IsSimplyConnected` is this definition, as explained in
`SimplyConnected/Basic.md`. A connected semisimple `k`-group is an actual group
scheme with `IsSemisimple`, which includes connectedness through
`IsConnectedReductive`.

Corollary A.4.11(1), printed p. 500 (PDF p. 526), reads: "Let G be a connected
semisimple k-group. There is a central isogeny π : G̃ → G from a connected
semisimple k-group G̃ that is simply connected. The pair (G̃, π) is unique up to
unique isomorphism, and its formation commutes with any extension of the base
field." The statement holds over every field `k`. The first sentence is the
existence part of this proposition: for semisimple `G` it produces `C = G̃` and
`π`, which give fields 1 to 3 of `IsSimplyConnectedCover π`. The Library's
central-isogeny convention (finite, flat, surjective, with central kernel) is
compared with the source convention in `CentralIsogeny/Basic.md`. The
corollary's proof (printed pp. 500–501, PDF pp. 526–527) reduces by Galois
descent to separably closed `k`. It then takes the character lattice dual to the
coroot lattice and uses Theorem A.4.10. That is a proof route, not a hypothesis
here.

### The unique-factorization law: Milne, Propositions 18.8 and 19.15

CGP states that the pair is unique up to unique isomorphism. It does not state
that `π` factors through every central isogeny onto `G`. Field 4 comes from
Milne. Milne, Definition 18.5 (printed p. 388, PDF p. 404), calls a connected
group variety simply connected if every multiplicative isogeny onto it from a
connected group variety is an isomorphism. Definition 18.7 (printed p. 389,
PDF p. 405) defines a universal covering of `G` as a multiplicative isogeny
`G̃ → G` with `G̃` a simply connected connected group variety. Proposition
18.8 (printed p. 389, PDF p. 405) says the following. Let `π : G̃ → G` be a
universal covering, assume that `k` or `G` is perfect, and let
`φ : G′ → G` be a multiplicative isogeny of connected group varieties. Then
there is a unique homomorphism `α` with `π = φ ∘ α`. The printed text says
that the target of `α` is `G`. The errata snapshot corrects this: "p.389. In
the statement of 18.8, the target of α is G′, not G. This is correct in the
diagram." So `α : G̃ → G′`.

The two sources' conventions agree for semisimple groups:

- Milne, Proposition 19.15 (printed p. 400, PDF p. 416) says that a semisimple
  group `G` is simply connected if and only if every central isogeny `G′ → G`
  from a semisimple `G′` is an isomorphism. Its proof (printed p. 401, PDF
  p. 417) begins: "When G is semisimple, to say that an isogeny G′ → G is
  central with G′ semisimple is the same as saying that it is multiplicative
  with G′ a connected group variety." The text after the proof calls the
  second condition "the usual definition of 'simply connected' for semisimple
  groups (see, for example, Conrad et al. 2015, p. 500)". So for semisimple
  `G`, Milne's test isogenies in 18.8 are exactly the central isogenies from
  semisimple groups. These are the test maps `q : H ⟶ G` of
  `HasCentralCoverUniversalProperty`. For the same reason, the CGP cover
  `π : G̃ → G` is a universal covering in Milne's sense.
- The perfectness hypothesis of 18.8 holds for semisimple `G` over every field:
  Milne, Corollary 21.50 (printed p. 440, PDF p. 456), says "Every semisimple
  algebraic group is perfect."

Applying 18.8 to the CGP cover, with the corrected arrow, gives: for every
central isogeny `q : H → G` from a semisimple `H` there is a unique
`a : G̃ → H` with `π = q ∘ a`. This is field 4, `a ≫ q = π`.

Packaging this law inside the conclusion is derived content. The proposition
asserts the conjunction of CGP's existence statement and Milne's factorization
property for the produced cover. Neither source states this conjunction as one
result. The statement adds no hypothesis, and in particular it does not assume
that simple connectedness implies the law. A separate statement task,
"State the unique-factorization law for semisimple simply connected central
covers" (`2be094ba-099b-4960-b5e3-3326c4320317`), states that implication for a
simply connected source and a central isogeny. A proof of this proposition may use that result once it is proved, or
it may verify the law directly.

## What is not stated

- Field-extension compatibility, the last clause of CGP Corollary A.4.11(1),
  is not part of this proposition. It is a separate statement successor.
- Uniqueness of the cover is not restated; it follows from the conclusion
  through the published `IsSimplyConnectedCover.iso` and `iso_unique`.
- Nothing is proved here. The existence of `C` and `π`, and the verification
  of all four fields of `IsSimplyConnectedCover π` over arbitrary fields, are the
  obligation of a separate exact-target proof.
