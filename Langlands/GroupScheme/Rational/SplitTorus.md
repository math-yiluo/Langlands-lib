# Split subtori, maximal split tori, the split rank and anisotropy over a field

Author: Worker 1220.

This module starts the rational structure layer for group schemes over a field.
It defines split subtori and maximal split tori of a group scheme
`G : GroupScheme S` over `S = Spec k`, the split rank (`k`-rank) of `G` and
anisotropy. It also proves the elementary consequences of these definitions that
need no further theory. All declarations are in the namespace
`Langlands.GroupScheme`. Throughout, `k : Type u` is a field and
`S = Spec (CommRingCat.of k)`.

## Sources

- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 4.21 (printed p.93, PDF p.40): « Les tores déployés sur k maximaux de G
    sont conjugués sur k. »
  - 4.23 (printed p.93, PDF p.40): « La dimension (commune vu 4.21) des tores
    déployés sur k maximaux de G est le k-rang de G [...] Le groupe G est
    anisotrope sur k si son k-rang est nul [...] »
- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Definition 25.3 (printed p.545, PDF p.561): "A reductive group is isotropic
    if it contains a noncentral split torus; otherwise, it is anisotropic."
    Footnote: "Some authors define a reductive group to be isotropic if it
    contains a nontrivial split torus. The two definitions agree for semisimple
    groups."
  - Theorem 25.10 (printed p.546, PDF p.562): "Any two maximal split tori in G
    are conjugate by an element of G(k)."

In both sources `G` is a connected reductive group over `k`. The definitions
below are stated for every group scheme over `S`. This generality is derived:
the predicates make sense without reductivity. The theorems that need
reductivity, such as the conjugacy of maximal split tori, are not stated in this
module. They are planned deliverables of the same task, to be stated later with
the published `IsConnectedReductive` in a separate statement module; no such
module exists yet.

## Split subtori and maximal split tori

A torus homomorphism is `i : T.toGrp ⟶ G` with `T : CommGroupScheme S`, the
published commutative group schemes.

- `IsSplitSubtorus i := IsSplitTorus T.toGrp ∧ IsClosedSubgroup i`. Here
  `IsSplitTorus` (module `Langlands.GroupScheme.Torus.Split`) says that `T` is
  isomorphic, as a group scheme over `S`, to `splitTorus S I = 𝔾ₘ^I` for a
  finite `I`. `IsClosedSubgroup i` (module `Langlands.GroupScheme.Reductive.Basic`)
  says that the underlying morphism of schemes is a closed immersion. This is a
  "torus defined over `k` and split over `k`" in `G`, the *tore déployé sur k*
  of Borel–Tits and the split torus in `G` of Milne. The sources take
  subgroups; here a subgroup is given by a closed-immersion homomorphism.
- `IsMaximalSplitTorus i` holds when `IsSplitSubtorus i` holds and, for every
  commutative `T'`, every `i' : T'.toGrp ⟶ G` with `IsSplitSubtorus i'` and
  every `f : T.toGrp ⟶ T'.toGrp` with `f ≫ i' = i`, the map `f` is an
  isomorphism (`IsIso f`). This is maximality for inclusion among split
  subtori: `i` does not factor through a strictly larger split subtorus.
  `IsMaximalSplitTorus.isSplitSubtorus` extracts the first conjunct.

## The split rank and anisotropy

- `splitRank G : ℕ∞` is the supremum of `Nat.card I` over finite `I : Type u`
  and homomorphisms `i : splitTorus S I ⟶ G` with `IsClosedSubgroup i`. Here
  `Nat.card I` is the rank of the split torus `𝔾ₘ^I`, the number of its
  factors; this module does not identify it with a scheme-theoretic dimension.
  The supremum over no tori is `0`.
- `IsAnisotropic G := splitRank G = 0`, following Borel–Tits 4.23.

Comparison with the sources.

- **Rank as a supremum.** Borel–Tits 4.23 defines the `k`-rank as the common
  dimension of the maximal `k`-split tori, which is well defined by the
  conjugacy theorem 4.21. Here the rank is the supremum over all closed split
  subtori, which makes sense for every group scheme. For connected reductive
  `G` the two should agree by conjugacy. That agreement is neither stated nor
  proved here: it is planned as part of a later conjugacy statement of this
  task, which is not yet written. The value `⊤` is allowed by the type; it does
  not occur for algebraic groups, which is not proved here either.
- **Anisotropy convention.** Milne 25.3 calls a reductive `G` anisotropic when
  it has no *noncentral* split torus. Here, following Borel–Tits 4.23, `G` is
  anisotropic when it has no nontrivial split torus at all. So `𝔾ₘ` is
  anisotropic for Milne but not here: `one_le_splitRank_gm` and
  `not_isAnisotropic_gm` below. As Milne's footnote says, the two conventions
  agree for semisimple groups (not formalized here).

## Lemmas

- `IsClosedSubgroup.of_iso e`: an isomorphism of group schemes is a closed
  subgroup, since its underlying scheme morphism is an isomorphism.
- `IsClosedSubgroup.iso_comp e hi`: precomposing a closed subgroup
  `i : H ⟶ G` with an isomorphism `e.hom : H' ⟶ H` of group schemes gives a
  closed subgroup. The underlying scheme morphism is an isomorphism followed by
  a closed immersion.
- `card_le_splitRank I i hi`: a closed homomorphism `splitTorus S I ⟶ G` has
  `Nat.card I ≤ splitRank G`. This is `le_iSup` four times.
- `IsSplitSubtorus.card_le_splitRank hi I e`: if `i` is a split subtorus and
  `e : T.toGrp ≅ splitTorus S I`, then `Nat.card I ≤ splitRank G`. It applies
  the previous lemma to `e.inv ≫ i`, which is closed by `iso_comp`.
- `isAnisotropic_iff`: `IsAnisotropic G` holds exactly when every closed
  homomorphism `splitTorus S I ⟶ G` has `I` empty. Forward: `Nat.card I ≤ 0`
  forces `Nat.card I = 0`, and a finite type of cardinality zero is empty.
  Backward: every term of the supremum is `Nat.card I = 0`.
- `IsAnisotropic.isEmpty_of_isSplitSubtorus hG hi I e`: in an anisotropic `G`,
  every split subtorus `i` with `e : T.toGrp ≅ splitTorus S I` has `I` empty.
- `one_le_splitRank_gm`: `1 ≤ splitRank 𝔾ₘ`. The published isomorphism
  `splitTorus.gmIso : 𝔾ₘ ≅ splitTorus S PUnit` gives the closed homomorphism
  `(gmIso S).inv : splitTorus S PUnit ⟶ 𝔾ₘ`, and `Nat.card PUnit = 1`.
- `not_isAnisotropic_gm`: `𝔾ₘ` is not anisotropic in the sense of this module.
- `splitTorus.subsingleton_hom_of_isEmpty I H`, over any base scheme: for empty
  `I` there is at most one homomorphism `splitTorus S I ⟶ H`. Every point of
  `splitTorus S I` is `1`, because `splitTorus.pointsEquiv` identifies the points
  with the one-element group `I → Γ(U, 𝒪_U)ˣ`. Applied to the identity point,
  this gives `f.hom.hom = 𝟙 ≫ f.hom.hom = 1 ≫ f.hom.hom = 1` for every
  homomorphism `f` (`MonObj.one_comp`), and `Grp.hom_ext` concludes.
- `IsAnisotropic.subsingleton_hom_of_isSplitSubtorus hG hi H`: in an
  anisotropic `G`, a split subtorus `T` has at most one homomorphism to any
  group scheme `H`. It transports the previous lemma along `e`.
- `IsAnisotropic.subsingleton_character hG hi`: in an anisotropic `G`, a split
  subtorus `T` has at most one homomorphism `T ⟶ Gm S` of commutative group
  schemes. Its character group is therefore trivial. This is the only form of
  the triviality proved in this module.

## Pending work

The task also asks for the anisotropy consequence in terms of the character
lattice and the roots: in an anisotropic `G`, a split subtorus has
`characterLattice T = 0` and empty `roots i`. Those two names are definitions
of a sibling task that are not yet published, so that form is **not** proved
here. It remains pending; its planned place is a later relative-roots module of
this task, which will import those definitions and derive it from
`IsAnisotropic.subsingleton_character`.
