# Bernstein's second adjointness from its remaining inputs

Authors: Worker 1402 and Worker 937. Module
`Langlands.Representation.Exponents.LeviSecondAdjointnessFromInputsStatement`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The module contains one `Prop`-valued definition,
`LeviSecondAdjointnessFromInputsStatement.{u, v}`. It is neither assumed nor proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.9.6: the first Theorem (VI.9.6.1) (printed p.201 / PDF p.207) and its
proof. The proof first derives (VI.9.6.1) from the second Theorem (VI.9.6.2) (printed
pp.201–202 / PDF pp.207–208), then proves (VI.9.6.2) through the Proposition of VI.9.6
(printed pp.202–205 / PDF pp.208–211). The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The conclusion is the
published `LeviSecondAdjointnessStatement`; see `LeviSecondAdjointnessStatement.md`.

## The statement

`LeviSecondAdjointnessFromInputsStatement.{u, v}` is an iterated implication. Its
conclusion is `LeviSecondAdjointnessStatement.{u, v}`. That statement covers
nonarchimedean local fields `k : Type u` and connected reductive `G`. For every
represented parabolic `P = MN` and every represented parabolic `P̄ = M N̄` with the same
Levi and `P(F) ∩ P̄(F) = M(F)`, the published normalized induction
`leviInductionFunctor.{u, max u v}` of `P` is left adjoint to the published normalized
Jacquet functor `leviJacquetFunctor.{u, max u v}` of `P̄`. Its premises are seven
published propositions, in this order:

1. `ParabolicDynamicStatement.{u}` (Milne, Theorem 25.1): a closed subgroup of a connected
   reductive group is parabolic if and only if its range is the dynamic `P(χ)` of a
   cocharacter `χ`.
2. `OppositeDynamicParabolicUniquenessStatement.{u}` (Borel–Tits 1965, 4.8 and 4.10): if
   `Z(χ') = Z(χ)` and the rational points of `P(χ)` and `P(χ')` meet exactly in those of
   `Z(χ)`, then `P(χ')` and `U(χ')` are the dynamic parabolic and unipotent radical of
   `χ⁻¹`.
3. `RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v}` (Renard
   VI.9.1, Proposition). Its inputs are a cocharacter `χ`, a compact open subgroup `K`, and
   an element `g` that commutes with every point of `Z(χ)(F)` and satisfies
   `Jacquet.IsIwahoriContraction K N M N̄ g` for `N = U(χ)(F)`, `M = Z(χ)(F)` and
   `N̄ = U(χ⁻¹)(F)`. It concludes only that there is an exponent `b` such that, for every
   smooth representation `V` with carrier in `Type (max u v)`, the power ranges and power
   kernels of the compressed action `v ↦ e_K(π(g)v)` on `V^K` are constant from `b` on, and
   the stable image and the kernel supremum split `V^K`
   (`Jacquet.CompactCompressionSplits`).
4. `Dynamic.LeviAdjointDeterminantReciprocityStatement.{u}`: for a maximal split torus
   and a cocharacter `ζ` of it, the determinant characters of the adjoint actions of
   `Z(ζ)` on `Lie U(ζ)` and on `Lie U(-ζ)` add to zero.
5. `RationalPointFamily.RationalReductiveUnimodularityStatement.{u}`: rational points of
   connected reductive groups over nonarchimedean local fields are unimodular. This
   statement takes the next premise as an argument.
6. `StandardCocharacterStatement.{u}`: standard cocharacters exist, and standard subgroups
   are the corresponding dynamic subgroups.
7. `ArbitraryParabolicQuotientCompactStatement.{u}`: `P(F) \ G(F)` is compact for every
   represented parabolic `P`.

## Why these premises

They are the published results that the proof of (VI.9.6.1) uses in the
represented-parabolic interface and that are not yet proved in the Library. Renard proves
(VI.9.6.1) from the uniform stabilization of VI.9.1, which gives a pairing between the
Jacquet modules `r_P(V)` and `r_{P̄}(Ṽ)` (Casselman's pairing, the Proposition of VI.9.6),
and from the description of the contragredient of an induced representation (III.2.7).
In that proof:

- Premises 1 and 2 put `P`, `M`, `N` and `N̄` in dynamic form. Premise 1, together with
  the proved Library theorem `dynamicGeometricUnipotentRadical` (the identity-limit
  subgroup `U(χ)` is the geometric unipotent radical of `P(χ)`), gives a cocharacter `χ`
  with `P(F) = P(χ)(F)`, `M(F) = Z(χ)(F)` and `N(F) = U(χ)(F)`. Premise 2 identifies
  `N̄(F)` with `U(χ⁻¹)(F)`, using the two hypotheses on `P̄` in the target. Renard takes
  the opposite parabolic as given with its Levi.
- The contracting element and the subgroups `K` come from proved Library theorems, not
  from a premise. `BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint`
  gives a point `g ∈ Z(χ)(F)` that commutes with `Z(χ)(F)`, whose powers contract
  `U(χ)(F)` and whose inverse powers contract `U(χ⁻¹)(F)`. From this,
  `Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` gives
  `Jacquet.HasOppositeIwahoriContractionBasis`: every identity neighbourhood contains a
  compact open subgroup `K` with `IsIwahoriContraction K N M N̄ g` and
  `IsIwahoriContraction K N̄ M N g⁻¹`. The published proof of
  `RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis`
  (`ArbitraryParabolicJacquetAdmissibilityReduction.lean`) takes the same route.
- Premise 3, at carrier universe `max u v`, is applied to each such `K` in both orders: to
  `χ` with `g`, and to `χ⁻¹` with `g⁻¹` (since `Z(χ⁻¹) = Z(χ)`, the second contraction
  condition above is the input for `χ⁻¹`). It supplies the uniform stabilization exponent
  and the splitting of `V^K` behind Casselman's pairing for the representations of `G(F)`
  in the adjunction.
- Premise 4 shows that the Haar scaling characters of conjugation by `M(F)` on `N(F)` and
  on `N̄(F)` are inverse to each other. Casselman's pairing needs this to match the
  normalizations of `r_P` and `r_{P̄}` (Renard, printed p.205, citing lemma V.5.4).
- Premises 5 and 6 give unimodularity of `G(F)` and of `M(F)`, hence the modular character
  of `P(F)` (Renard V.5.4). Premise 7 gives compactness of `P(F) \ G(F)`. With these, the
  contragredient of `i_P^G τ` is `i_P^G τ̃` for every smooth `τ` (Renard III.2.7).

`DynamicGeometricUnipotentRadicalStatement` is not a premise, because the Library proves
it.

## Faithfulness notes

- **No change to the target.** The conclusion is the published target statement at the
  same universes `u, v`. Every premise is a published proposition used at its own
  universes. No premise mentions the specific `G`, `P`, `P̄` or representation of the
  target, so this is a plain implication between closed statements.
- **Universes.** Premise 3 is used at carrier universe `max u v`, the carrier universe of
  both functors in the target.
- **Strength.** All premises are results of the literature or published statements with
  their own provenance. None of them is the target or contains it. The companion
  statement `LeviJacquetContragredientFromInputsStatement` uses premises 1 to 4 only, with
  premise 3 at carrier universe `v`.

## Provenance

Derived. The statement records which published inputs the proof of Renard VI.9.6
(VI.9.6.1) needs in the represented-parabolic interface. Its premises are exactly the
hypotheses of the reduction theorem `leviSecondAdjointness_of_structure` in the shared
draft of task `c0fa1878-6cee-4435-8484-2fc15ea04a17` (revision 22, module
`Exponents/LeviSecondAdjointnessStructure`). Revision 2 of that task lists this statement
and its proof under "Intermediate conditional results". The statement lets that
conditional proof be reviewed and published separately from the proofs of its inputs. Combining it with proofs
of the seven premises gives the target.
