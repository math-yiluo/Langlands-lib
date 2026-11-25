# Statement: maximal tori of anisotropic real groups are conjugate

`Langlands.GroupScheme.RealAnisotropicMaximalTorusConjugacyStatement : Prop` is
a statement-only, `Prop`-valued definition with no universe parameters. This
module does not prove it, and it adds no other definitions, theorems or
axioms. It imports:

- [`Reductive.Semisimple`](../Reductive/Semisimple.md), for `IsSemisimple`.
  Through its import of `Rational.SplitRankTransport` it also brings in
  [`Rational.SplitTorus`](SplitTorus.md), for `IsAnisotropic`.
- [`Torus.Maximal`](../Torus/Maximal.md), for `IsMaximalTorus`. Through its
  imports it also brings in inner automorphisms `innerIso`
  ([`InnerAutomorphism`](../InnerAutomorphism.md)) and subgroup functors
  `SubgroupFunctor.range` ([`SubgroupFunctor`](../SubgroupFunctor.md)).

## Lean statement

```lean
def RealAnisotropicMaximalTorusConjugacyStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G → IsAnisotropic G →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of ℝ))) (j : T.toGrp ⟶ G)
      (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of ℝ))) ⟶ G.X,
          SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j'
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S`
  the commutative group schemes; `T.toGrp` is the underlying group scheme of
  `T`. For `G : GroupScheme S`, `G.X` is its scheme over `S`. A point of `G`
  over the base is a morphism `Over.mk (𝟙 S) ⟶ G.X`. For `S = Spec ℝ` these
  are the real points `G(ℝ)`.
- `IsSemisimple G` ([`Reductive.Semisimple`](../Reductive/Semisimple.md)):
  `G` is connected reductive (`IsConnectedReductive`: smooth, affine,
  connected, with trivial geometric unipotent radical) and its
  scheme-theoretic centre is finite.
- `IsAnisotropic G` ([`Rational.SplitTorus`](SplitTorus.md)):
  `splitRank G = 0`. Here `splitRank G` is the supremum of `Nat.card I` over
  finite index types `I` that admit a closed-subgroup homomorphism
  `splitTorus (Spec ℝ) I ⟶ G`, where `splitTorus S I` is `𝔾ₘ^I`. So
  `IsAnisotropic G` says that `G` contains no split torus of positive
  dimension (`isAnisotropic_iff`).
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)) for
  `j : T.toGrp ⟶ G`: `T` is a torus (`IsTorus`), `j` is a closed immersion
  (`IsClosedSubgroup`), and whenever `j` factors as `f ≫ j''` through a torus
  `j'' : T'' ⟶ G` that is a closed immersion, `f` is an isomorphism. So `T`
  is a torus of `G` not properly contained in a larger torus of `G`.
- `G.innerIso g` for a real point `g`
  ([`InnerAutomorphism`](../InnerAutomorphism.md)): the inner automorphism
  of `G` that sends a point `x` over any `U` to `g x g⁻¹`
  (`comp_innerIso_hom`, in the same module).
- `SubgroupFunctor.range i` for `i : H ⟶ G`: the subgroup functor of `G`
  whose points over `U` are the points of `G` over `U` that factor through
  `i`. Equality of two ranges says that the two subgroups have the same
  points over every scheme `U` over `Spec ℝ`. For closed immersions this
  says that they are the same closed subgroup of `G`.

## Statement in words

Let `G` be a semisimple group over `ℝ` that is anisotropic, that is,
contains no nontrivial split torus. Let `j : T ⟶ G` and `j' : T' ⟶ G` be
maximal tori. Then there is a real point `g ∈ G(ℝ)` such that conjugation by
`g` carries `T` onto `T'`: `range (j ≫ int(g)) = range j'`, that is,
`g T g⁻¹ = T'` as subgroups of `G`.

## Source

J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type
over a field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page numbers
are printed page numbers; the PDF page is the printed page plus 16.

- Theorem 25.57, p. 561: "THEOREM 25.57 (CARTAN). Let G be an anisotropic
  semisimple algebraic group over R. Then any two maximal tori in G are
  conjugate by an element of G(R)." Proof: "For a short proof, see Suzuki
  1971, Theorem 2."
- Definition 25.3, p. 545: "A reductive group is isotropic if it contains a
  noncentral split torus; otherwise, it is anisotropic." The next sentences
  read: "Thus, the isotropic reductive groups are those containing a proper
  parabolic subgroup. A semisimple group is isotropic if and only if contains
  a nontrivial split torus." Its footnote ends: "Some authors define a
  reductive group to be isotropic if it contains a nontrivial split torus.
  The two definitions agree for semisimple groups."
- Conventions, p. 4: "After p. 162, all algebraic groups are affine."
  Chapter 25 opening, p. 544: "Recall that all algebraic groups are affine
  over a base field k."
- 6.44, p. 135: "A connected group variety over a field k is semisimple if
  G_{k^a} is semisimple, i.e., if its geometric radical R(G_{k^a}) is
  trivial."
- Theorem 17.82, p. 379: "Let G be a group variety over k and let k′ be a
  field containing k. A torus T in G is maximal if and only if T_{k′} is
  maximal in G_{k′}." Section 17d, p. 363, defines a maximal torus over a
  general field by maximality of `T_{k^a}` in `G_{k^a}` and says: "Later
  (17.82) we shall see that this agrees with the obvious definition."

The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; the PDF page
is the printed page plus 11) has Theorem 25.57 on printed p. 564 as "Let G be
an anisotropic semisimple algebraic group over R. Any two maximal tori in G
are conjugate by an element of G(R)", with the same proof reference. Its
Definition 25.3, on printed p. 548, reads: "A semisimple group is isotropic
if it contains a nontrivial split torus; otherwise, it is anisotropic." Its
footnote says that some authors call a reductive group isotropic if it
contains a nontrivial split torus (Borel 1991) and others (Springer 1994) only
if it contains a noncentral split torus, and ends: "We avoid the term except
for semisimple groups and tori." Its Theorem 17.82, on printed p. 379, reads:
"A torus T is maximal among the tori in G if and only if T_{k′} is maximal
among the tori G_{k′}." (The missing "in" is in the source.) Its 6.44 is on printed p. 135 with the same
wording.

Errata. The errata snapshot of 2026-11-02 for the 2017 book (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 135, 363, 379, 544 or 561. Its entry "p.545 et
seq." concerns 25.6(b), 25.24 and 25.27 (the parabolic subgroup should be
minimal), not Definition 25.3. The errata snapshot of 2026-11-04 for the 2022
reprint (source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 4, 135, 379, 548 or 564.

## Derivation from the source (provenance: derived)

- **Semisimple group over ℝ.** Milne's algebraic groups are affine (p. 4,
  p. 544), and a semisimple group is a connected group variety (6.44).
  `IsSemisimple G` contains `IsConnectedReductive G`, which includes
  smoothness, affineness and connectedness. The Library's `IsSemisimple`
  uses the finite-centre characterization of semisimplicity among connected
  reductive groups, as recorded in
  [`Reductive.Semisimple`](../Reductive/Semisimple.md).
- **Anisotropic.** For a semisimple group, both editions call `G`
  anisotropic when it contains no nontrivial split torus (2017: the sentence
  after Definition 25.3 and its footnote; 2022: Definition 25.3 itself).
  This is `IsAnisotropic G` (split rank zero); see
  [`Rational.SplitTorus`](SplitTorus.md) for the comparison of the Library's
  split rank with the split tori of the sources.
- **Maximal tori.** Theorem 17.82 shows that Milne's maximal tori are the
  tori of `G` that are maximal among the tori of `G` over `ℝ`. This is
  `IsMaximalTorus` over `ℝ`.
- **Conjugate by an element of G(ℝ).** A real point `g` is a morphism
  `Over.mk (𝟙 (Spec ℝ)) ⟶ G.X`, and "`T` and `T'` are conjugate by `g`" is
  `g T g⁻¹ = T'`, expressed as equality of subgroup functors. Since `g`
  ranges over a group, the direction of conjugation does not matter.
- No universe parameter: the base field `ℝ : Type` fixes the universe.

Sanity check. `SL_2` over `ℝ` is semisimple but not anisotropic: it contains
the split diagonal torus. It also contains the torus `SO(2)`, whose real
points form a circle. These two maximal tori are not conjugate over `ℝ`,
since a conjugate of a split torus is split and `SO(2)` is not. So the
anisotropy hypothesis is needed. Its anisotropic form `SU(2)`, the norm-one
group of the Hamilton quaternions, satisfies the conclusion: every maximal
torus is conjugate under `SU(2)(ℝ)` to the diagonal circle.

## Relation to the Library

- `MaximalTorusSeparableConjugacyStatement`
  ([`Torus.MaximalSeparableConjugacyStatement`](../Torus/MaximalSeparableConjugacyStatement.md),
  Milne 17.87) gives conjugacy of maximal tori after a finite separable
  extension, and over the base field when it is separably closed. Over `ℝ`
  it only gives conjugacy over `ℂ`. The present statement gives conjugacy
  over `ℝ` for anisotropic semisimple groups.
- The Library has no other statement of Theorem 25.57; it proves this one as
  `realAnisotropicMaximalTorusConjugacy`
  ([`RealAnisotropicMaximalTorusConjugacyProof`](RealAnisotropicMaximalTorusConjugacyProof.md)).

## For a proof (not part of this module)

Milne gives no proof; he refers to Suzuki 1971, Theorem 2.
