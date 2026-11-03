# Statements: existence and central isogenies of split reductive groups, and semisimplicity

Authors: Worker 1391 (original draft), Worker 1466 (source verification and preparation).

This module states three unproved propositions about split reductive groups over
an arbitrary field. Each is a `Prop`-valued `def` in the namespace
`Langlands.GroupScheme`, with one universe parameter `u`. Nothing is proved
here.

- `SplitReductiveExistenceStatement`: every reduced root datum is the root
  datum of a split connected reductive group (the Existence Theorem).
- `SplitCentralIsogenyExistenceStatement`: every central isogeny of root data
  between two split connected reductive groups comes from a central isogeny of
  the groups (the existence half of the Isogeny Theorem, central case).
- `SplitSemisimpleRootDatumStatement`: a split connected reductive group is
  semisimple exactly when its root datum is semisimple.

The module imports `Langlands.GroupScheme.Reductive.RootDatumStatement`,
`Langlands.GroupScheme.Reductive.Semisimple`,
`Langlands.GroupScheme.CentralIsogeny.Basic` and
`Mathlib.LinearAlgebra.RootSystem.Hom`. It introduces no definition other than
the three propositions. It reuses by name the Library declarations
`GroupScheme`, `CommGroupScheme`, `CommGroupScheme.groupHom`,
`IsConnectedReductive`, `IsConnectedReductive.isAffineHom`, `IsSemisimple`,
`IsSplitTorus`, `IsMaximalTorus`, `characterLattice`, `cocharacterLattice`,
`IsRootDatumOf` and `IsCentralIsogeny`, and Mathlib's `RootDatum`,
`RootPairing.IsReduced`, `RootPairing.Equiv`, `RootPairing.Hom`,
`RootPairing.rootSpan` and `RootPairing.corootSpan`.

## Common conventions

- `k : Type u` is an arbitrary field in an arbitrary universe `u`. There is no
  perfectness, separable-closedness or characteristic hypothesis.
- Group schemes are actual group objects of `Over (Spec k)`
  (`GroupScheme S = Grp (Over S)`); tori are commutative group schemes
  `T : CommGroupScheme (Spec k)`, and `i : T.toGrp ⟶ G` is an actual
  homomorphism.
- A *split connected reductive group* in the sense of Milne, "split reductive
  group `(G, T)`", is written as the hypotheses `IsConnectedReductive G`,
  `IsSplitTorus T.toGrp` and `IsMaximalTorus i`. These are exactly the
  hypotheses of the published `RootDatumExistenceStatement`.
- `characterLattice T = (T ⟶ Gm)` and `cocharacterLattice T = (Gm ⟶ T)` are the
  Library's actual character and cocharacter groups.
- `IsRootDatumOf i P` (module `Reductive.RootDatum`) says that the Mathlib root
  datum `P` on these lattices has the Library's lattice pairing as its pairing,
  that its roots are exactly the actual roots `roots i` (the nonzero weights of
  `T` on `Lie(G)(k)`), and that each reflection of `P` is induced by a point of
  `G` normalizing `i`. It needs the instance `IsAffineHom G.X.hom`, which each
  statement takes from `hG.isAffineHom` by `haveI`, as
  `RootDatumExistenceStatement` does.
- Mathlib's `RootDatum J X Y` is a root pairing over `ℤ`: a perfect pairing
  `X × Y → ℤ` with roots `J ↪ X` and coroots `J ↪ Y` satisfying the reflection
  axioms. These are Milne's root data (Milne, printed p.483), except that
  reducedness is a separate predicate `RootPairing.IsReduced`.

## `SplitReductiveExistenceStatement`

```lean
def SplitReductiveExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (J X Y : Type u) [Finite J] [AddCommGroup X] [AddCommGroup Y]
    [Module.Finite ℤ X] (P : RootDatum J X Y), P.IsReduced →
      ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
        (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsSplitTorus T.toGrp ∧ IsMaximalTorus i ∧
          haveI := hG.isAffineHom
          ∃ Q : RootDatum J (characterLattice T) (cocharacterLattice T),
            IsRootDatumOf i Q ∧ Nonempty (RootPairing.Equiv P Q)
```

For every field `k` and every reduced root datum `P` with finitely many roots
on a finitely generated lattice `X`, there are an actual connected reductive
group `G` over `Spec k`, a split maximal torus `i : T ⟶ G`, and a root datum `Q`
of `i`, indexed by the same type `J`, that is isomorphic to `P` as a root
pairing. A `RootPairing.Equiv P Q` is a linear isomorphism `X ≃ X(T)` with the
transposed isomorphism `Y(T) ≃ Y`, together with a bijection of index sets,
matching roots with roots and coroots with coroots.

The hypothesis `Module.Finite ℤ X` makes `X` finitely generated. The perfect
pairing makes `X` torsion-free and identifies `Y` with its integral dual, so
both are lattices; no separate finiteness hypothesis on `Y` is needed.

**Source.** Milne, Theorem 23.55 (Existence Theorem), printed p.501 / PDF
p.517, realizes every reduced root datum by a split reductive group over the
field `k`. His reducedness convention (printed p.483, PDF p.499) is the
explicit hypothesis `P.IsReduced` here. Realization is expressed by an
isomorphism between the given root datum and that of `(G, T)`. Milne,
Theorem 23.74 (printed p.511, PDF p.527) obtains realizations over every field
from one smooth group scheme over `ℤ`, citing Demazure and SGA 3, XXV.

## `SplitCentralIsogenyExistenceStatement`

```lean
def SplitCentralIsogenyExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (J J' : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T')),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
      ∀ f : RootPairing.Hom P' P, Function.Injective f.weightMap →
        Function.Injective f.coweightMap →
          ∃ (φ : G ⟶ G') (t : T ⟶ T'), i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
            (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧ IsCentralIsogeny φ
```

Let `(G, T, i)` and `(G', T', i')` be split connected reductive groups over `k`
with root data `P` and `P'`. Let `f : RootPairing.Hom P' P` be a morphism of
root pairings whose weight map `X(T') → X(T)` and coweight map `Y(T) → Y(T')`
are injective. Then there are an actual homomorphism `φ : G ⟶ G'` and a
homomorphism of commutative group schemes `t : T ⟶ T'` such that

- `i ≫ φ = groupHom t ≫ i'`, so `φ` maps `T` into `T'` through `t`;
- `f.weightMap χ = t ≫ χ` for every character `χ` of `T'`, so `f` is the map
  `X(t) : X(T') → X(T)` on characters;
- `IsCentralIsogeny φ`: the morphism underlying `φ` is finite, flat,
  surjective and locally of finite presentation, and its full scheme-theoretic
  kernel (on all test schemes, nonreduced ones included) is central.

**Matching Milne's central isogenies of root data.** Mathlib's
`RootPairing.Hom P' P` consists of a weight map `X(T') → X(T)`, a coweight map
`Y(T) → Y(T')` that is its transpose for the two perfect pairings, and a
bijection `J' ≃ J`, such that the weight map sends each root of `P'` to the
corresponding root of `P` and the coweight map sends each coroot of `P` to the
corresponding coroot of `P'`. Milne, Definition 23.1 (printed p.483, PDF
p.499) calls an injective `f : X' → X` with finite cokernel an isogeny of root
data `R' → R` if there are a bijection `α ↔ α'` and `q : Φ → p^ℕ` with
`f(α') = q(α)α` and `f^∨(α^∨) = q(α)α'^∨`; Definition 23.2 (printed p.484, PDF
p.500) calls it central if `q(α) = 1` for all `α`. Milne notes (printed
p.484) that injectivity with finite cokernel is equivalent to injectivity of
both `f` and its transpose `f^∨`. Thus a `RootPairing.Hom P' P` with
injective weight and coweight maps is exactly a central isogeny of root data
`R(G', T') → R(G, T)` in Milne's sense, with `f^∨` the coweight map.

**Source.** Milne, Theorem 23.9 (Isogeny Theorem), printed p.487 / PDF p.503:
for split reductive `(G, T)` and `(G', T')` over `k`, an isogeny of tori
`T → T'` extends to an isogeny `G → G'` exactly when its character map is an
isogeny of root data. Consequently every root-datum isogeny in the indicated
contravariant direction is induced by a group isogeny. Milne,
Proposition 23.5 (printed pp.485-486, PDF pp.501-502) shows that such an
isogeny is central exactly when the isogeny of root data is central. An
isogeny of split reductive groups maps `T` into `T'` (printed p.485), which
is the equation `i ≫ φ = groupHom t ≫ i'`. Milne's central isogeny (kernel
contained in the centre) and the Library's `IsCentralIsogeny` are compared in
`CentralIsogeny/Basic.md`.

**Derived packaging.** Milne's theorem starts from an isogeny of tori
`T → T'`. Here the torus homomorphism `t` is part of the conclusion and is
determined by `f` through `f.weightMap χ = t ≫ χ`. This form is chosen because
the Library has no anti-equivalence between split tori and their character
lattices, and a user typically has only the lattice map `f`. A proof must
construct `t` from `f` as well as `φ`; Milne, Theorem 12.9(a) (printed p.233,
PDF p.249), the anti-equivalence between diagonalizable groups and finitely
generated commutative groups, provides it in the source. Only the existence
half of the Isogeny Theorem is stated. Proposition 23.7 separately describes
the ambiguity using inner automorphisms defined by `(T'/Z(G'))(k)`.

## `SplitSemisimpleRootDatumStatement`

```lean
def SplitSemisimpleRootDatumStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P →
          (IsSemisimple G ↔ Finite (characterLattice T ⧸ P.rootSpan ℤ)) ∧
            (IsSemisimple G ↔ Finite (cocharacterLattice T ⧸ P.corootSpan ℤ))
```

For a split connected reductive group `(G, T, i)` over `k` with root datum `P`,
`G` is semisimple (`IsSemisimple G`: connected reductive with finite full
centre) exactly when the roots span a subgroup of finite index in `X(T)`, and
exactly when the coroots span a subgroup of finite index in `Y(T)`. Here
`P.rootSpan ℤ` and `P.corootSpan ℤ` are the `ℤ`-submodules spanned by the roots
and coroots.

**Source.** Milne, Proposition 21.48 (printed p.439, PDF p.455), equates
semisimplicity of the group with semisimplicity of its root datum. Definition
C.34, recalled there, defines the latter by finite index of `ℤΦ` in `X`.
This gives the first equivalence; its proof uses the finite-centre criterion
of Proposition 19.10 (printed p.400, PDF p.416), matching `IsSemisimple`.
The second equivalence is derived by root-system duality: the rational root
and coroot spans have the same rank, while the perfectly paired ambient
lattices have equal rank. A subgroup of a lattice has finite index exactly
when its rational span has full rank. Milne uses this dual finite-index
conclusion for the coroots in the proof of Proposition 21.49(a), on the same
page as Proposition 21.48. The statement packages both forms together; the
dual equivalence remains part of the eventual proof obligation.

## Sources

- J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
- Milne's official errata, snapshot of 2026-11-02, source
  `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`. It lists
  no correction to Definitions 23.1-23.2, Proposition 23.5, Theorem 23.9,
  Theorem 23.55, Theorem 23.74 or Proposition 21.48.

## What is not stated

- Uniqueness: the Isomorphism Theorem (Milne 23.25-23.26) and the uniqueness
  half of the Isogeny Theorem (Milne 23.7) are not stated.
- Non-central isogenies (`q(α) ≠ 1`, for example Frobenius isogenies) are not
  covered by `SplitCentralIsogenyExistenceStatement`.
- Nothing here asserts simple connectedness; the coroot criterion for simple
  connectedness is a separate statement.
