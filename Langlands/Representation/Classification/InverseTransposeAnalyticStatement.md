# Analytic inverse-transpose transport

Author: Worker 17.

This module states two internal analytic transport obligations for actual
p-adic general linear groups. Its declarations are `Prop`-valued definitions;
the module proves neither equivalence.

## Statements and quantifiers

The declarations lie in `Langlands.Classification`. Fix a prime `p`,
`F : PadicField.{uF} p`, and `T : F.TopologicalData`. For every positive
integer `n`, every complex module `V : Type uV`, and every representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`, write
`ι = GeneralLinear.inverseTranspose n F.Carrier`. This is the actual
automorphism `g ↦ (g⁻¹)ᵀ`. The pullback is the representation
`ρ.comp ι.toMonoidHom` on the same carrier `V`.

- `InverseTransposeTemperedClause T` states
  `T.IsTempered (ρ.comp ι.toMonoidHom) ↔ T.IsTempered ρ`.
- `InverseTransposeSquareIntegrableClause T` states
  `T.IsSquareIntegrable (ρ.comp ι.toMonoidHom) ↔ T.IsSquareIntegrable ρ`.
- `PadicInverseTransposeAnalyticStatement` quantifies over every prime, field
  and compatible topological realization and conjoins the two clauses.

The field universe `uF` and representation-carrier universe `uV` are
independent. The carrier is arbitrary in `Type uV`, without a constraint
`uV = uF` or a forced `max uF uV`. A carrier lifted by `ULift` can be used
by instantiating `uV` with the resulting universe; this places no restriction
on the lift universe relative to the field or original carrier. No topology
or finite-dimensionality assumption is imposed on `V`.

There is no irreducibility, unitarizability, classification, exhaustion,
measure-invariance or supplied transport-map hypothesis. Smoothness and
admissibility are not added as separate premises: admissibility, including
smoothness, is already part of each analytic predicate.

## Unchanged analytic predicates

The module imports
[Classification.Tempered](Tempered.md) without changing it. Its predicates use
the actual central quotient
`Q = GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`
with the quotient topology induced by `T` and its Borel measurable structure.
They quantify over **every** Borel Haar measure `μ` on `Q`.
`T.exists_isHaarMeasure_centralQuotient n` ensures that this quantification
is not vacuous.

For each such measure, the predicate requires admissibility and a
`UnitaryCentralCharacter ρ`: an actual scalar action of the center through a
character with open kernel and values of norm one. It then requires
`MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal (2 + ε)) μ`
for every smooth-dual functional `ℓ`, vector `v`, and real `ε > 0` in the
tempered case, or `MemLp (c.coefficientNorm ℓ v) 2 μ` in the square-integrable
case. The central-character witness is inside the quantification over measures,
as in the imported predicates. The definition of `coefficientNorm` and the
square-integrable predicate are in
[MatrixCoefficient.ModuloCenter](../MatrixCoefficient/ModuloCenter.md).

## Internal provenance and eventual proof obligations

These statements are derived internal obligations from the imported analytic
definitions and the concrete group automorphism, rather than transcriptions
of a separately cited classification theorem. The following describes the
intended change-of-variables argument and the work still required for a proof.

1. [Group.GL.Maps](../../Group/GL/Maps.md) supplies
   `GeneralLinear.inverseTransposeContinuous`, the p-adic specialization
   `T.generalLinearInverseTranspose n`, and
   `GeneralLinear.inverseTranspose_involutive`. One must restrict this
   automorphism to the center and descend it to a continuous group
   automorphism, hence a homeomorphism `ῑ`, of the actual central quotient.
   Its formula must be `ῑ(gZ) = ι(g)Z`. The quotient map and its compatibility
   are obligations, not inputs to either clause.
2. Pullback along the continuous group automorphism must preserve and reflect
   smoothness and admissibility. Compact open subgroups correspond under
   the automorphism; fixed vectors for the pulled-back representation
   correspond to fixed vectors for the original representation at the
   image subgroup. This must transport finite-dimensionality of those
   fixed-vector spaces. Smooth-dual functionals must correspond as well,
   by comparing their open stabilizers under the automorphism.
3. A unitary central character must pull back along the induced automorphism
   of the center, preserving its open kernel, unit norm and scalar-action
   condition. With corresponding smooth-dual functionals, one must prove
   the descended coefficient identity
   `c_pull.coefficientNorm ℓ v = (c.coefficientNorm ℓ v) ∘ ῑ`.
   The same underlying linear functional and vector occur on both sides.
4. For an arbitrary Borel Haar measure `μ` on `Q`, the pushforward
   `Measure.map ῑ μ` must again be a Borel Haar measure. A measurable
   change-of-variables argument for the quotient homeomorphism must compare
   `MemLp (f ∘ ῑ) q μ` with `MemLp f q (Measure.map ῑ μ)`.
   Apply this with `q = 2` and with
   `q = ENNReal.ofReal (2 + ε)` for every `ε > 0`.
5. Apply the same transport again and use involutivity to obtain the reverse
   implication, with the representation composition identities checked.

Quantification over all Haar measures permits applying the original analytic
predicate to the transported measure. The argument does not require an
assertion that an arbitrary selected Haar measure is preserved exactly, or
a normalization of such a measure. This module supplies neither the
Haar-transport theorem nor the `MemLp` comparison.

The existing `T.isTempered_iff_of_equiv` and
`T.isSquareIntegrable_iff_of_equiv` transport representations along an
equivalence for a fixed acting group. They do not by themselves identify an
arbitrary representation with its inverse-transpose pullback.
Substantial missing constructions for the eventual proof should be developed
as separate prerequisites. The present module introduces no new transport
data object and gives no block-induction presentation of temperedness.
It makes no identification of the pullback with the smooth contragredient.
