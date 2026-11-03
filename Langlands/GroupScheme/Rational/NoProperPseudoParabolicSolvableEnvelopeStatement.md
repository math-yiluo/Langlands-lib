# A solvable envelope in the absence of proper pseudo-parabolic subgroups

Author: Worker 1367.

Worker 1305 prepared this derived prerequisite and Worker 1295 coordinated
the common subgroup and factorization interface used here.

`Langlands.GroupScheme.NoProperPseudoParabolicSolvableEnvelopeStatement.{u}`
is an unproved proposition at arbitrary universe `u`. For every field
`k : Type u` and actual group scheme `G` over
`Spec (CommRingCat.of k)`, it assumes that `G` is smooth, connected and
affine and that

```text
∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
  IsPseudoParabolicSubgroup i → IsIso i.
```

It concludes that there are an actual group scheme `H` over the same base
and a homomorphism `j : H ⟶ G` such that:

- `IsClosedSubgroup j`;
- `Smooth H.X.hom`, `ConnectedSpace H.X.left` and `IsAffineHom H.X.hom`;
- `IsSolvableGroupScheme H`;
- for every commutative group scheme `S` over the same base and every
  `i : S.toGrp ⟶ G` satisfying `IsSplitSubtorus i`, there exists a group
  scheme homomorphism `f : S.toGrp ⟶ H` with `f ≫ j = i`.

The existential quantifiers for `H` and `j` precede the universal quantifiers
for `S` and `i`: one subgroup serves every split subtorus. The equality is
between actual group scheme homomorphisms over `k`, so it gives the
factorization on every relative scheme test. No conjugation or field
extension is needed in this conclusion. The statement permits `H = G` and
claims no strict dimension inequality. All fields, including finite and
imperfect fields in positive characteristic, are included.

## Published interfaces

The module imports the public definitions unchanged from
`Langlands.GroupScheme.PseudoParabolic`,
`Langlands.GroupScheme.Rational.SplitTorus` and
`Langlands.GroupScheme.Absolute.Borel`. The pseudo-parabolic module imports
the separately published
`Langlands.GroupScheme.Reductive.UnipotentRadical` and
`Langlands.GroupScheme.SubgroupFunctor.FppfProduct` modules.

`IsPseudoParabolicSubgroup i` uses a ground-field cocharacter and the
represented fppf-local product of its dynamic parabolic with a ground-field
unipotent radical. It entails closedness of `i`. The no-proper-subgroup
hypothesis ranges over every such inclusion and requires it to be an
isomorphism. Here “proper subgroup” means an inclusion which is not an
isomorphism; it does not mean a proper morphism or a proper quotient.

`IsClosedSubgroup j` says that the underlying scheme map is a closed
immersion. `IsSplitSubtorus i` says that `S.toGrp` is a split torus and
`i` is a closed subgroup. `IsSolvableGroupScheme H` is the published
solvability condition on the abstract group of geometric points after
base change to an algebraic closure. The conclusion separately requires
smoothness of `H`, as appropriate for that condition. These predicates
are used directly; none is replaced by containment on rational points.

## Source and derived provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The relevant passages are Lemma 2.2.3(1), printed pp.62–63 (PDF pp.88–89),
and the proof of Theorem C.2.3, printed pp.593–594 (PDF pp.619–620).
These passages were read in the registered second edition. No project
errata file for this source was present when this statement was prepared.

This statement is derived from the first branch of the proof of
Theorem C.2.3. It is not the verbatim assertion of Lemma 2.2.3, nor does
it assert the full maximal split torus conjugacy theorem. Write
`U = R_{u,k}(G)` for the ground-field unipotent radical. Lemma 2.2.3(1)
identifies existence of a proper pseudo-parabolic subgroup with existence
of a noncentral split torus in `G/U`. In the branch where no such subgroup
exists, the proof of Theorem C.2.3 takes the maximal central split torus
`C` of `G/U` and observes that every split torus of `G` maps into `C`.
Its inverse image `H` in `G` is smooth, connected and solvable and
contains all split tori. Affineness and closedness come from this inverse
image construction inside the affine group `G`. Expressing the resulting
subgroup containments through actual homomorphisms gives the conclusion
recorded here.

## Retained proof obligations

This file defines a proposition and supplies no proof of it. A subsequent
proof must establish the existence and properties of the represented
ground-field radical, construct its quotient, and justify the comparison
of the published pseudo-parabolic predicate with the quotient criterion
of Lemma 2.2.3(1). It must construct the maximal central split torus in that
quotient and show that every split subtorus of `G` maps into it. It must
then construct the inverse image as an actual closed group scheme,
prove its smoothness, connectedness and affineness, and prove its
solvability in the published geometric-points sense. Finally, it must
produce the actual factorization `f ≫ j = i` over `k` for every split
subtorus through the same `H` and `j`.

These radical, quotient, central split torus, solvability and factorization
obligations are not hypotheses of the statement. No theorem-valued premise
encodes them, and importing the definition modules does not discharge them.
