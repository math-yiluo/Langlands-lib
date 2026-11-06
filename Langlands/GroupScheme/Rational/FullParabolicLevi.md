# Rational Levi inclusions into a full reductive group

This internal supporting construction is for the conjugacy step of Renard
2026, VII.2.6, printed pages 231–232 / PDF pages 237–238. It uses the published
definitions of a rational Levi and connected reductivity, the actual Levi
retraction, and the theorem that a connected reductive group has trivial
ground-field unipotent radical. It introduces no new structural premise
discharger beyond this consequence of those results.

For any field `k : Type u`, if `l : M ⟶ P` is a rational Levi inclusion and
`P` is connected reductive, `isIso_of_connectedReductive` proves that `l`
is an isomorphism of group schemes. Choose a geometric unipotent radical
`r : U ⟶ P` with the multiplication isomorphism supplied by the rational
Levi definition. Reductivity makes its range the trivial subgroup functor.
The existing Levi retraction is a left inverse of `l`; the exact
Levi-times-radical decomposition, evaluated on every test scheme, makes it
a right inverse as well.

`isoOfConnectedReductive` returns the resulting isomorphism with forward
map exactly `l`. If a morphism `p : P ⟶ G` is an isomorphism and `G` is
connected reductive, `isIso_of_isIso_parabolic` transports reductivity
across `p` and applies the first result. `isoOfIsIsoParabolic` returns the
isomorphism `M ≅ G` whose forward map is exactly `l ≫ p`. No separate
parabolicity hypothesis is required for this implication.

`rationalLeviConjugacyOfFullParabolics` applies this to two intersection
parabolics `p₁ : P₁ ⟶ M₁` and `p₂ : P₂ ⟶ M₂`, each assumed an isomorphism.
For their rational Levi inclusions `l₁` and `l₂`, an isomorphism
`φ : L₂ ≅ L₁`, two ambient maps `m₁ : M₁ ⟶ G` and `m₂ : M₂ ⟶ G`, and an
automorphism `a : G ≅ G`, it takes the equation
`φ.hom ≫ l₁ ≫ p₁ ≫ m₁ = l₂ ≫ p₂ ≫ m₂ ≫ a.hom`.
It returns an actual isomorphism `e : M₁ ≅ M₂` with
`e.hom ≫ m₂ = m₁ ≫ a.inv`. The construction composes the inverse of the
first full Levi isomorphism, `φ.symm`, and the second full Levi isomorphism.
Its ambient equation follows by composing the input equation with the
inverse maps. Taking `a` to be inner conjugation by a rational point gives
the group-scheme equation required in the uniqueness statement, with the
inverse conjugating point.

All assertions hold over arbitrary fields and for the original actual
group schemes, with no rational-point or topology substitution. This unit
does not prove that an intersection parabolic arising in the geometric
lemma is full, identify its representations, or prove any of the three
VII.2.6 statements. Those are separate obligations.
