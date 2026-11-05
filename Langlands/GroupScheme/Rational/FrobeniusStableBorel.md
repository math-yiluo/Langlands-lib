# Frobenius-stable Borels from explicit Borel conjugacy

Construction by Worker 1601; interface design with Worker 59.

This supporting construction takes the exact Library proposition
`BorelConjugacyStatement.{u}` as an explicit premise. For a finite field
`k : Type u` with a `Fintype` instance, an algebraic algebraically closed
extension `Ω : Type u`, and a smooth connected affine group scheme `G/k`,
`exists_frobeniusStableBorel_of_borelConjugacy` supplies an actual inclusion
`i : B ⟶ G_Ω` that is Borel and whose subgroup functor is fixed by the
cardinality-of-`k` Frobenius automorphism of `Ω`. The equality uses
`SubgroupFunctor.galoisTransport` and holds on every relative test scheme.
There is no restriction on characteristic or the common universe `u`.
Taking `Ω := AlgebraicClosure k` gives the geometric Borel needed for the
finite-field quasi-splitness argument.

The implementation first obtains smoothness and affineness of `G_Ω` by
base change and connectedness by
`connectedSpace_baseChange_of_smooth_affine`. Given a Borel inclusion `i`,
pull it back along the Frobenius automorphism of `Spec Ω` and compose with
the canonical `descentBaseChangeIso` identifying the pulled-back ambient
group with `G_Ω`. The field automorphism is an isomorphism of schemes.
Thus `IsBorelSubgroup.baseChange_of_isIso` and
`IsBorelSubgroup.comp_iso` show that this transformed inclusion is Borel.
The supplied conjugacy statement gives `SubgroupConjugate F(i) i`,
including its rational conjugating point and source-group isomorphism.

The published Lang construction `frobeniusStableConjugate` then supplies
an actual conjugate `j` of `i`, with the same source group, whose
Frobenius-transported all-test range equals its range. The new lemma
`IsBorelSubgroup.frobeniusStableConjugate` preserves the Borel property by
ambient-isomorphism transport. The supplied-Borel lemmas retain the
conjugacy `SubgroupConjugate i j` and give both the explicit transported
inclusion range equation and its equivalent `galoisTransport` form.
`SubgroupFunctor.descentTransport_range` identifies these formulations.
Finally the existence part of `BorelConjugacyStatement` supplies the
initial Borel, giving the main existential theorem.

`FrobeniusStableBorelData k Ω G` retains this actual source group,
inclusion, Borel proof and all-test Frobenius invariance together.
`frobeniusStableBorelDataOfBorelConjugacy` chooses such data using the
existential theorem. It has the same hypotheses as that theorem and
makes no uniqueness or canonical-choice claim.

The direct Library inputs are `Absolute.BorelStatement`,
`Absolute.ParabolicBorelFactorization`, `GeometricConnectedness`, and
`Torus.FrobeniusConjugate`; these also import the Borel-isomorphism and
subgroup-transport interfaces used above. The latter module already
implements Lang's equation and the resulting all-test range identity.
This module is an internal composition of those proved interfaces and
the explicit conjugacy premise.

The mathematical route is the Frobenius-invariance step in Milne,
*Algebraic Groups*, corrected 2022 reprint, Proposition 17.99,
printed p.384 (one-based PDF p.395), registered source
`milne-2022-algebraic-groups`. The retained author errata for that reprint
has no correction to this passage. This unit does not prove Borel
conjugacy or descend the invariant Borel to `k`; those remain separate
inputs to the unconditional `FiniteFieldQuasiSplitStatement`.
