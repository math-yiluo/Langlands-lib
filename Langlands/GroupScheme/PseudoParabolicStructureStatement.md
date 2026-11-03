# Structure of pseudo-parabolic subgroups

`Langlands.GroupScheme.PseudoParabolicSubgroupStructureStatement.{u}` is
an unproved proposition target. For every field `k : Type u`, actual group
schemes `G,P` over `Spec (CommRingCat.of k)`, and actual homomorphism
`i : P ⟶ G`, it asserts

```text
Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
  IsPseudoParabolicSubgroup i →
    Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧ IsAffineHom P.X.hom.
```

The three ambient hypotheses are typeclass binders in Lean. Smoothness and
affineness refer to the structure morphism; connectedness is ordinary
connectedness of the underlying scheme. The statement covers finite and
imperfect fields in arbitrary universe `u`. It requires neither reductivity
nor pseudo-reductivity.

The module imports the published
`Langlands.GroupScheme.PseudoParabolic` unchanged. Its
`IsPseudoParabolicSubgroup i` already includes the three ambient properties
and a represented product presentation. They are repeated as explicit
ambient hypotheses to expose the intended geometric setting. The supplied
map `i` remains the subgroup inclusion: the existing
`IsPseudoParabolicSubgroup.isClosedSubgroup` extracts `IsClosedSubgroup i`.
The conclusion concerns this same `P`, without changing the representative.

The imported predicate uses the ground-field unipotent radical from
`Langlands.GroupScheme.Reductive.UnipotentRadical` and the all-test
fppf-local product from
`Langlands.GroupScheme.SubgroupFunctor.FppfProduct`. In particular, it does
not require the radical to be split or identify it with a geometric radical,
and it does not replace a subgroup scheme by its rational points. Smoothness
and connectedness of `P` are absent from that definition; this target records
the additional structure theorem.

## Source and derived provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Definition 2.2.1 is on printed p.62 (PDF p.88).
Proposition 2.1.8(3)–(4), on printed p.53 (PDF p.79), gives smoothness and
connectedness of the dynamic parabolic; its proof continues through printed
p.57 (PDF p.83).

This target is a derived structural consequence of those results and the
smooth connected normal ground-field unipotent radical used in Definition
2.2.1. It is not presented as a verbatim numbered theorem in that passage.
A proof must establish the geometry of the represented subgroup product,
including its correspondence with the imported fppf-local presentation.
Affineness also uses the actual closed inclusion into affine `G`. None of
those geometric steps is proved by this statement module.

This module defines a `Prop` and supplies no proof or new instance. It makes
no quotient, pseudo-completeness, properness, or rational-conjugacy assertion.
