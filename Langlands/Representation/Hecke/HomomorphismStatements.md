# Continuous-homomorphism restriction and induction: statements

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, using
III.1.4, printed p.60 / PDF p.66, and the Theorem of I.2.3, printed p.18 /
PDF p.24. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This file contains closed `Prop`-valued definitions. It proves none of them.
Its objects are the actual bimodule and four functors from
`HomomorphismLeft`, `HomomorphismRight` and `HomomorphismSmooth`, on the
original Hecke algebras and the published Chapter I tensor/Hom constructions.

`HeckeInductionAdjunctionStatement` asserts both canonical adjunctions,
`F ⊣ I` and `P ⊣ pseudoF`, by specializing the published propositions
`NondegenerateInductionAdjunction.CanonicalFInductionAdjunction` and
`CanonicalPInductionAdjunction`. Their conclusions contain the actual
adjunctions, additive Hom equivalences, their precise evaluation formulas,
the inverse quotient lifts, naturality, units, counits and triangle laws.
The specified actions are the constructed subgroup actions and ordinary
regular multiplication, so no unrelated action certificates are inputs.

`SmoothInductionAdjunctionStatement` asserts existence of equivalence proofs
for the two exact `heckeNondegenerateModuleFunctor`s of III.1.4, and then:

- a natural isomorphism from the existing smooth pullback `Fφ` of
  (III.2.1.1) to the transported tensor functor `smoothF`;
- the adjunction `smoothF ⊣ smoothI`;
- the adjunction `smoothP ⊣ smoothPseudoF`.

The source writes `Fφ = F_H^G` after identifying the smooth and Hecke-module
categories. The statement uses a natural isomorphism because the tensor
construction has the actual balanced quotient as its carrier, whereas
pullback keeps the original carrier. It does not assert literal equality
of those distinct carrier constructions.

The III.1.4 equivalences are conclusions of this closed statement. They
are not additional hypotheses weakening Renard's assertion. Once obtained,
their proof terms are the explicit inputs to the previously constructed
transport functors. The statement keeps the Hausdorff, locally compact
nonarchimedean hypotheses of a t.d. group in II.1.1, arbitrary continuous
homomorphisms, supplied left Haar measures and independent universes
`uG`, `uH`, `v`. Adjunctions are expressed at carrier universe
`max uG v`, stable under the original tensor/Hom functors; no relation
between `uH` and the other universes is required.

`ContinuousHomomorphismStatements` is exactly the conjunction of these
two targets. Proofs belong to a separate `lean.proof@1` task after the
statement is published.
