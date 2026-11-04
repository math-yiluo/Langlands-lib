# Split radical containment for pseudo-parabolic subgroups

This module defines the proposition
`Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentStatement.{u}`.
It states that for a pseudo-parabolic
`P = P_G(χ) R_{u,k}(G)`, the two factors `U_G(χ)` and `R_{us,k}(G)` lie in
`R_{us,k}(P)`, viewed as subgroup functors of `G`. Together these are the
containment `U_G(χ) R_{us,k}(G) ⊆ R_{us,k}(P)`.
The module contains a single `Prop`-valued definition and no proof.

## Original source

The source is Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive
groups*, second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The readable original is
`/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
Corollary 2.2.5 is stated on printed p.64 (one-based PDF p.90), with proof
on printed pp.64–65 (PDF pp.90–91). The split containment stated here is
established in the first paragraph of its proof, on printed p.64.
No errata note for this source was present in the current public notes.

That paragraph uses Proposition A.1.4 on split unipotent quotients,
Proposition 2.1.10 on the split smooth connected unipotent subgroup
`U_G(λ)`, and Proposition 2.2.4 on the product presentation with the split
radical. It identifies `U_G(λ) R_{us,k}(G)` as a split smooth connected
unipotent normal subgroup of `P` and invokes the defining maximality of
`R_{us,k}(P)`. These inputs describe the source argument; they are neither
proved here nor added as premises. Lean uses `χ` for the source's `λ`.

## Data and the two radicals

The proposition quantifies over every field `k : Type u` at arbitrary
universe `u`, and every actual group scheme `G` over
`B = Spec (CommRingCat.of k)` with
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[ConnectedSpace G.X.left]`. It then takes:

- an actual homomorphism `r : R ⟶ G` satisfying `IsUnipotentRadical r`;
- an actual cocharacter `χ : (Gm B).toGrp ⟶ G`;
- an actual homomorphism `i : P ⟶ G` satisfying
  `(Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range r) i`;
- actual homomorphisms `n : V ⟶ G` and `m : W ⟶ P` satisfying
  `IsSplitUnipotentRadical n` and `IsSplitUnipotentRadical m`.

The first radical is the ordinary ground-field unipotent radical
`R_{u,k}(G)`: its all-test image is greatest among smooth connected
unipotent normal closed subgroups over `k`. The split predicates additionally
require the existing finite-series predicate
`RelativeRoot.IsSplitUnipotent`, and greatestness only among split
competitors. Thus `n` represents `R_{us,k}(G)` and `m` represents
`R_{us,k}(P)`. The ordinary and split radicals are distinct notions over
imperfect fields. No geometric radical or identification of these two
notions is used. All imported predicates are unchanged.

## Products and all relative tests

The hypothesis on `i` is the presentation used by
`IsPseudoParabolicSubgroup`. It requires `i` to be a closed subgroup and
characterizes its image on every `T : Over B` as the fppf-local product
of `Dynamic.parabolic χ` and `SubgroupFunctor.range r`. Explicitly, a
point `x : T ⟶ G.X` lies in that image precisely when, after a flat,
surjective, locally finitely presented map `v : T' ⟶ T`, it factors as
`v ≫ x = p * a` with `p` in the dynamic parabolic and `a` in the image
of `r`. No factorization on the original test is assumed.

The conclusion is exactly

```lean
Dynamic.unipotent χ ≤ SubgroupFunctor.range (m ≫ i) ∧
  SubgroupFunctor.range n ≤ SubgroupFunctor.range (m ≫ i)
```

Here `Dynamic.unipotent χ` is the existing dynamic subgroup functor
`U_G(χ)`. The composite `m ≫ i` views the split radical of `P` inside
`G`. Each inequality means containment for every relative scheme `T` and
every point `x : T ⟶ G.X`, including nonaffine and nonreduced tests.
It is not restricted to rational or geometric points.

A subgroup containing both factors contains their products. Because the
target is represented by a closed subgroup, membership also descends from
an fppf cover. The two containments therefore express containment of the
fppf-local product without choosing a separate representative for
`U_G(χ) R_{us,k}(G)` or replacing that product by a pointwise subgroup join.

## Scope

The quantifiers retain finite and imperfect fields and every characteristic.
No reductivity, pseudo-reductivity, perfectness, infinitude, local sections
or theorem-valued premise is added. The radical representatives and the
product representative are supplied data; this definition asserts no
existence theorem and supplies no proof of the proposition.
The reverse split containment and the ordinary-radical equality from
Corollary 2.2.5 are outside this statement.
