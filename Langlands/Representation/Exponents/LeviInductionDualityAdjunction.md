# First adjointness and induction duality on represented Levi points

Author: Worker 138. Namespace `Langlands.Aubert.General.RepresentedParabolic`.

This internal adapter provides the unconditional Frobenius and induction-duality inputs
to David Renard's Hom chain (VI.9.6.3), *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, printed pp.201–202 / PDF pp.207–208. The underlying
source statements are VI.1.2 Proposition (first adjointness) and IV.2.1.2 (normalized
induction commuting with the contragredient). Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Fix a nonarchimedean local field `k : Type u`, and a represented parabolic `p : P ⟶ G`
with rational Levi `m : M ⟶ P`, matching geometric unipotent radical `n : N ⟶ P`, and
isomorphic subgroup multiplication `M × N → P`. The ambient rational-point group has
its canonical topology and is assumed locally compact and nonarchimedean. The topology
on `M(k)` is the published `leviPointTopology m hm`. Carriers are in `max u v`, with
independent universes `u` and `v`.

`leviFirstAdjointnessAdjunction` constructs the categorical adjunction
`leviJacquetFunctor p m n … ⊣ leviInductionFunctor p m n …`. It composes the published
first adjointness on the literal Levi image with the adjunction of the pullback
equivalence induced by `leviPointsEquiv`. The radical's unimodularity premise is supplied
by `isUnimodularModulus_pointImage_radical`.

`nonempty_leviInductionContragredientIso` additionally assumes `G` is connected reductive
and proves the existence of a natural isomorphism `(i_P).op ⋙ D_G ≅ D_M ⋙ i_P` for all
smooth complex representations. Compactness of the parabolic quotient is supplied by
`arbitraryParabolicQuotientCompact`. The ambient unimodularity and parabolic modular
character formulas come from `rationalReductiveUnimodularity`, `standardCocharacter`
and the published adapters in `LeviParabolicModulus`. Together with continuity of the
Levi projection, these yield the integral natural duality of the literal induction from
`exists_isNaturalIntegralDuality_of_compactSpace`. Whiskering that isomorphism and
`contragredientPullbackNatIso` with the appropriate functors transports it to `M(k)`.
Functor associators supply the parentheses.

No admissibility or finiteness restriction is imposed on the representations. This
module establishes the two inputs; it does not establish second adjointness.
