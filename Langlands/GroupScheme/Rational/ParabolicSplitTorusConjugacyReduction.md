# Conjugacy of maximal split tori inside a parabolic subgroup

This module is an internal conditional reduction for the existing proposition
`MinimalParabolicSplitTorusConjugacyStatement`. The Prop-valued definition
`ParabolicSplitTorusConjugacyInputs.{u}` bundles the three explicit hypotheses
`SmoothMaximalSplitTorusConjugacyStatement`, `ParabolicDynamicStatement`, and
`DynamicConnectedStatement` as their conjunction, at an arbitrary universe `u`.
The final theorem takes a proof of this bundle as its premise. This internal
interface supplies no proof of these structural statements and does not by
itself prove the unconditional target.

The reduction applies over every field, including finite and imperfect fields.
The conjugating point belongs to the ground-field points of the given subgroup
`P`, and the resulting equation is between the given torus factorizations as
group scheme homomorphisms into `P`:

```lean
f ≫ (P.innerIso p).hom = e.hom ≫ f'
```

The proof has four steps, corresponding to the four Lean lemmas.

- `exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations` works
  with an arbitrary closed subgroup `H` of an ambient group `G`, assuming
  that `H` is smooth, affine, and connected. The published
  `IsMaximalSplitTorus.of_comp` makes each given factorization of an ambient
  maximal split torus a maximal split torus of `H`. Applying the conjugacy
  hypothesis directly to `H` gives the rational point of `H`, the isomorphism
  of the torus sources, and the equation into `H`. No reductivity of `G` or
  `H` is required for this step.
- `IsParabolicSubgroup.connectedSpace_of_parabolicDynamic` applies the
  parabolic-dynamic hypothesis to express the all-test range of `j : P ⟶ G`
  as `Dynamic.parabolic χ` for a cocharacter over the ground field. The closed
  immersion underlying `j` is a monomorphism, so this equality makes `j` a
  representative of that subgroup functor. The parabolic clause of dynamic
  connectedness, using the smoothness, affineness, and connectedness supplied
  by `IsConnectedReductive G`, then gives connectedness of `P`.
- `exists_parabolic_innerIso_comp_eq_of_structuralStatements` obtains
  smoothness of `P` and closedness of `j` from `IsParabolicSubgroup j`.
  The composite of this closed immersion with the affine structure morphism
  of `G` is affine, giving affineness of `P`. The preceding connectedness
  lemma supplies the last hypothesis needed to apply the first step.
  This proves the conjugacy conclusion for any parabolic containing the two
  ambient maximal split tori.
- `minimalParabolicSplitTorusConjugacy_of_structuralStatements` unpacks
  `ParabolicSplitTorusConjugacyInputs` and specializes that result to a minimal parabolic using only its parabolic property. Its
  conclusion is the unchanged published proposition imported from
  `Rational.ParabolicTorusStatement`. Minimality is unnecessary for the
  intermediate conjugacy result.

The provenance of this internal deduction is the application of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Theorem C.2.3, printed p.593 (PDF p.619), inside `P` itself. The proof of
Proposition C.2.4, printed pp.594–595 (PDF pp.620–621), uses the same passage
to conjugacy inside a parabolic. The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The two explicit structural
hypotheses used for connectedness are the published interfaces for
parabolic-dynamic comparison and CGP Proposition 2.1.8(4). The implementation
uses those hypotheses exactly as stated. It does not use relative Weyl
groups, rational Bruhat covering, relative root systems, or Tits systems.
