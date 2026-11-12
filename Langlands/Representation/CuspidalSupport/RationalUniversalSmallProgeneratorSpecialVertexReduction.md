# Renard VI.4.1 for the full-restriction Π₁ from the special-vertex inputs

Worker 4959, Task 4959 (`0ba788d6-b9d9-4a76-a017-972f8cad288f`). This module
states and proves a conditional reduction of the unconditional target
`Langlands.CuspidalSupport.RationalUniversalSmallProgeneratorStatement.{uF, uV}`.
It does not prove that target. The target, its structural binders and its
Lean/Markdown pair are unchanged.

## Statement

`RationalUniversalSmallProgeneratorSpecialVertexReductionStatement.{uF, uV}` is
the implication

`RationalSpecialVertexCompactInputsStatement.{uF} → RationalUniversalSmallProgeneratorStatement.{uF, uV}`.

Both sides are published propositions.

- The premise, from module
  `Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction`,
  says the following. Take every nonarchimedean local field `F : Type uF`, every
  connected reductive group scheme `G` over `F`, every maximal split torus
  inclusion `i` and every generic cocharacter `ν`. Then there are an apartment
  datum `D : KPApartmentData i (localFieldOrder F)` and a special apartment
  vertex `x`. The subgroup `K0 = D.specialCompactSubgroup x` has
  `SpecialCompactProperties`, `SimultaneousStandardBasisAt` and the covering
  clause `FiniteCartanCovering` of the Cartan decomposition.
- The conclusion is the VI.4.1 target for the alternative progenerator
  Π₁ = `rationalNormKernelCompactInduction G π`, the compact induction of the
  entire restriction of π to the common rational-character norm kernel. For
  every irreducible π that is cuspidal along all proper actual standard
  parabolics, it asserts `IsRationalNormKernelSmallProgenerator G π`. This
  means that Π₁ is in the block
  `RationalInertiaBlock G (rationalInertiaBaseLift G π)`, and that in this
  block Π₁ has the projective lifting property and a faithful integer Hom
  functor. It also means that the block has coproducts indexed by
  `Type (max uF uV)` and that this Hom functor preserves them.

The field universe `uF` and the representation-carrier universe `uV` are
independent. The premise involves only `uF`.

## Proof

`rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction`
takes the premise, `RationalNormKernelFiniteRestrictionStatement.{uF, uV}`
(Renard VI.3.2(ii)) and
`RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}`
(Renard VI.3.2(iii)) as hypotheses. It introduces every binder of the target:
the field, the group, the torus inclusion, the three topological instances,
the cocharacter, `StandardCocharacterStatement`, the relative root system,
closedness of the standard unipotent subgroups, the derived semidirect
decompositions, and an irreducible cuspidal π. It then proceeds in three steps.

1. The premise, applied to `F`, `G`, `i` and `ν`, gives `D`, `x` and the
   three properties of `K0`, together with the special-vertex property.
2. The published VI.2.1 (a) ⇒ (c) theorem
   `Langlands.Aubert.General.rationalCuspidalCompactRestriction` is applied
   to these witnesses, to the target's own structural binders and to the
   cuspidality of π. It gives `HasCompactSmoothDualCoefficients` for the
   restriction of π to `Plancherel.rationalCommonNormKernel G`. This
   restriction is `SmoothRep.restrictSubgroup`, which is definitionally
   `π.representation.comp (rationalCommonNormKernel G).subtype`.
3. The published conditional assembly `rationalNormKernelSmallProgeneratorReduction`
   (module `RationalUniversalSmallProgeneratorReduction`) takes connected
   reductivity, irreducibility, these compact coefficients and the two VI.3.2
   statements. It returns `IsRationalNormKernelSmallProgenerator G π`. That
   module proves block membership from the finite restriction family, the
   compact-coefficient projectors and the twist criterion. It proves
   projective lifting and faithfulness from compact coefficients, and
   coproduct existence from the inertia-block closure. It proves Hom
   coproduct preservation from finite composition length of the
   restriction.

`rationalUniversalSmallProgeneratorSpecialVertexReduction` proves the
reduction statement. It discharges the two VI.3.2 hypotheses with the
published proofs `rationalNormKernelFiniteRestriction` (Task 4361) and
`rationalNormKernelTwistEquivalence` (Task 4372).

`rationalUniversalSmallProgenerator_of_jointBasis` derives the target from
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`.
It composes the published `rationalSpecialVertexCompactInputs_of_jointBasis`
with the reduction.

## Scope and provenance

The provenance is internal. The statement is an implication between two
published propositions and makes no new literature claim. Its shape follows
Renard, *Représentations des groupes réductifs p-adiques* (French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.1 Proposition
and the alternative-progenerator Remark, printed pp.149–150 / PDF pp.155–156.
Renard's proof of the Proposition uses three facts. The restriction of π to ⁰G is
a direct sum of compact irreducible representations (cited there from VI.3.2).
Compact representations are projective (IV.1.6). Restrictions of objects of the
block to ⁰G are semisimple. For Π₁ the Remark adds that the restriction of π has
finite length. Renard's π is supercuspidal. The target here measures
cuspidality by vanishing proper standard Jacquet modules, so compactness comes
from the published VI.2.1 (a) ⇒ (c) theorem. Its Lean statement retains the
special vertex, the simultaneous basis and the Cartan covering at `K0` as
hypotheses, and these are exactly what the premise supplies.

The published module `RationalSummandSmallProgeneratorReduction` proves the
analogous implication `rationalSummandSmallProgenerator_of_specialVertexInputs`
for the summand progenerators of `RationalSummandSmallProgeneratorStatement`.
This module covers the full-restriction Π₁ of
`RationalUniversalSmallProgeneratorStatement`, which that module does not
treat.

No abelianness, coproduct existence, block membership, admissibility, finite
dimension or progenerator property is assumed. The only unproved input is the
special-vertex existence premise. Its stronger joint form is the target of
proof task `8c39faa0-2a70-4fc4-a027-914987aba924`. Once either proposition is
proved, applying the theorems of this module to that proof proves the exact
target `RationalUniversalSmallProgeneratorStatement.{uF, uV}`.
