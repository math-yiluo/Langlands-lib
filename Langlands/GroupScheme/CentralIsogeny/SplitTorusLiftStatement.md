# Lifting split maximal tori through a central isogeny

Author: Worker 1414.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.CentralIsogenySplitMaximalTorusLiftStatement`. The
Lean file only defines the proposition. It contains no proof of it, and it
adds no other definitions, theorems or axioms.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`. The field may be imperfect, of positive
  characteristic, and need not be separably closed;
- group schemes `G H : GroupScheme (Spec (CommRingCat.of k))` with
  `IsConnectedReductive G` and `IsConnectedReductive H`. This published
  predicate from [`Reductive.Basic`](../Reductive/Basic.md) says that the
  group is smooth, affine and connected over `k`, and that its base change to
  an algebraic closure has trivial unipotent radical;
- a homomorphism `π : G ⟶ H` with `IsCentralIsogeny π`, the published
  predicate from [`CentralIsogeny.Basic`](Basic.md): the underlying morphism
  of schemes is finite, flat, surjective and locally of finite presentation,
  and the full scheme-theoretic kernel of `π` is central in `G`. The kernel
  may be nonreduced; no separability of `π` is assumed;
- a commutative group scheme `S` with `IsSplitTorus S.toGrp`, that is, `S` is
  isomorphic to `𝔾_m^I` for a finite index type `I`
  ([`Torus.Split`](../Torus/Split.md));
- a homomorphism `i : S.toGrp ⟶ H` with `IsMaximalTorus i`
  ([`Torus.Maximal`](../Torus/Maximal.md)): `S` is a torus, `i` is a closed
  subgroup, and `i` factors through no strictly larger closed torus of `H`.

## Conclusion

There exist a commutative group scheme `T`, a homomorphism
`j : T.toGrp ⟶ G` and a homomorphism `f : T ⟶ S` of commutative group
schemes such that

- `IsSplitTorus T.toGrp`: `T` is a split torus;
- `IsMaximalTorus j`: `j` is a maximal torus of `G`;
- `j ≫ π = CommGroupScheme.groupHom f ≫ i`: the composite `T → G → H` is
  the composite `T → S → H`. In other words, `π` maps the maximal torus `T`
  of `G` into the given maximal torus `S` of `H`, and `f` is the induced map.

So every split maximal torus of `H` has a split maximal torus of `G` above
it. The statement does not say that `f` is an isogeny or that `T` is the
whole preimage of `S`. Those facts hold, but they are not asserted here.

## Sources and provenance

The statement is derived from published results; the Lean form is not
verbatim. The derivation below is written here; it is not quoted.

**Borel–Tits.** A. Borel and J. Tits, *Compléments à l'article « Groupes
réductifs »*, Publ. Math. IHÉS 41 (1972), source ID
`borel-tits-1972-complements-groupes-reductifs`. The paper fixes "G un
k-groupe connexe réductif" throughout (printed p.253, PDF p.2). Théorème
(2.20)(ii), printed p.260 (PDF p.9), for a central surjective `k`-morphism
`f : G → G'`: "Les tores déployés sur k maximaux de G' (resp. G) sont les
images (resp. les tores déployés maximaux des images réciproques) des tores
déployés sur k maximaux de G (resp. G')." Définition (2.2) and
Remarque (2.3), printed p.254 (PDF p.3), say that `f` is central exactly
when its scheme-theoretic kernel lies in the centre. This matches
`IsCentralIsogeny`. Neither separability nor smoothness of the kernel is
assumed.

**Milne.** J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`:

- Proposition 17.20, printed pp.357–358 (PDF pp.373–374), over an
  algebraically closed field: a quotient map `q : G → Q` of connected group
  varieties maps a maximal torus onto a maximal torus.
- Theorem 17.82, printed p.379 (PDF p.395): "A torus T in G is maximal if
  and only if T_{k'} is maximal in G_{k'}" for every field extension
  `k'/k`.
- Definition 19.20, printed p.401 (PDF p.417): the rank of `G` is the
  dimension of a maximal torus in `G_{k^a}`. The text after it, printed
  p.402 (PDF p.418), notes that this equals the dimension of a maximal torus
  in `G` (by 17.82).

**Derivation.**

1. `S` is a maximal split torus of `H`. If `i` factors through a closed
   split torus `S'` of `H`, then `S'` is in particular a closed torus, so
   the factoring map `S → S'` is an isomorphism by maximality of `i`.
   (The Library records this implication as
   `IsMaximalTorus.isMaximalSplitTorus` in
   [`Torus.MaximalSplitComparison`](../Torus/MaximalSplitComparison.md).)
2. By Borel–Tits (2.20)(ii), applied to the central surjection `π`, there is
   a maximal `k`-split torus `T` of `G` with `π(T) = S`. In particular `T`
   is split.
3. The ranks of `G` and `H` are equal. Over `k^a`, the map `π` is a quotient
   map with finite kernel. By Milne 17.20 it maps a maximal torus of
   `G_{k^a}` onto a maximal torus of `H_{k^a}`, with finite kernel, so the
   two tori have the same dimension.
4. `T` is a maximal torus of `G`. Since `π` has finite kernel,
   `dim T = dim S`. By 17.82 and 19.20, `dim S = rank H = rank G`. Every
   torus of `G` has dimension at most `rank G`, because its base change to
   `k^a` lies in a maximal torus there. So a torus of `G` containing `T` has
   the same dimension as `T`. Both are connected and smooth, so it equals
   `T`.
5. Let `j` be the inclusion of `T`. Then `j ≫ π` lands in the closed subgroup
   `S`, so it factors as `f ≫ i` with `f : T → S` a homomorphism.

**Errata.** The project snapshot of Milne's errata
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for printed
pp.357, 358, 379, 401 or 402. No errata note for the Borel–Tits paper was
found. Its §5 corrections concern the 1965 article.

## Role in the Library

This statement is an internal step towards the coroot criterion
`SplitCorootSpanSimplyConnectedStatement` (Milne, Proposition 23.29) for
`IsSimplyConnectedFieldExtensionStatement` in
[`SimplyConnected.FieldExtensionStatement`](../SimplyConnected/FieldExtensionStatement.md).
In that argument, `π` is an arbitrary central isogeny onto a split
semisimple group. This statement supplies a split maximal torus of the
source group mapping into the given one. That is the setting of Milne's
Proposition 23.5, an isogeny of split reductive groups `(G, T) → (G', T')`
(printed p.485, PDF p.501). The published
`CentralSurjectionMaximalSplitTorusImageStatement` in
[`Rational.CentralSurjectionMaximalSplitTorusImageStatement`](../Rational/CentralSurjectionMaximalSplitTorusImageStatement.md)
concerns the image direction for maximal split tori. It does not produce a
maximal torus of the source, so it does not replace this statement.
