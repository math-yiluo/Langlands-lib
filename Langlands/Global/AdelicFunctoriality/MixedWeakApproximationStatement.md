# Mixed weak approximation by principal ideles

Authors: Worker 54; the formulation reuses Worker 226's published
`exists_principal_inv_mul_mem`.

## Statement

`Langlands.Global.AdelicFunctoriality.MixedPrincipalIdeleApproximation.{u}`
is a `Prop`-valued definition. For every number field `K : Type u`, let
`S : Finset (HeightOneSpectrum (𝓞 K))` be any finite set of finite places,
and let `a : IdeleGroup (𝓞 K) K` be any idele. Given sets

- `U p ⊆ (p.adicCompletion K)ˣ` for every finite place, with `U p` a
  neighborhood of `1` whenever `p ∈ S`;
- `V w ⊆ (w.Completion)ˣ` for every `w : InfinitePlace K`, with every
  `V w` a neighborhood of `1`;

the proposition asserts the existence of a single `α : Kˣ` such that the
finite coordinate of
`(IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a` belongs to `U p` for every
`p ∈ S`, and its infinite coordinate belongs to `V w` for every infinite
place `w` simultaneously. The witness is a unit of the field, so its value
is nonzero. The set `S` may be empty. The family `U` is defined at all finite
places for convenience; neither its neighborhood hypotheses nor the conclusion
constrain places outside `S`.

## Objects and topology

The idele group and principal embedding are the published actual
`NumberField.IdeleGroup` and `IdeleGroup.unitEmbedding`. The finite coordinate
is `Langlands.ClassField.Global.ideleCoordinate`, and the infinite coordinate
is `Langlands.ClassField.Global.ideleInfiniteCoordinate`, imported through
`IdeleArchimedean`. They are the unit maps induced by projecting an adele
to its corresponding completion. At a principal idele, their values in the
completion are respectively
`algebraMap K (p.adicCompletion K) (α : K)` and
`algebraMap K w.Completion (α : K)`.

The neighborhood filters are those of the standard unit-group topologies
on the actual finite and infinite completions. No arbitrary topology is
quantified over. The finite completion uses its usual adic topology, and
the infinite completion uses the topology of its absolute value.
Here the principal multiplier is a member of `Kˣ`; no local principal-unit
filtration or integrality condition is imposed on it.

## Provenance and scope

This is a derived interface for the approximation step in Artin and Tate,
*Class Field Theory* (2009), Chapter V §4, Theorem 2, printed p.17
(PDF p.26). In that proof, a principal multiplier makes an idele sufficiently
close to `1` at the finitely many exceptional places before local norm
preimages are selected. The present formulation isolates this approximation
step for number fields and arbitrary neighborhoods of `1`. Requiring
simultaneous conditions at all infinite places covers any chosen
archimedean subset by taking `V w = Set.univ` at unused places.
The source's extension, normality and cyclicity hypotheses belong to the
surrounding norm argument, and are not assumptions of this proposition.
No local-norm or global class-field-theory hypothesis appears.

The original PDF p.26 and appended errata p.202 were read. The errata contain
no correction to this passage. Registered source:
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
retained at `/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

The proposition matches Worker 226's existing theorem
`Langlands.Global.AdelicFunctoriality.exists_principal_inv_mul_mem`
in [MixedWeakApproximation](MixedWeakApproximation.md).
That module derives the result from
`AbsoluteValue.denseRange_algebraMap_pi`, proves the mixed finite/infinite
inequivalence of absolute values, transfers approximation to the completions,
and uses the open embedding of units to obtain the multiplicative conclusion.
Those facts are not hypotheses of this statement.

This file defines the exact proposition without adding a proof theorem.
Its separate proof follow-up can reuse the published theorem. Local norm
neighborhoods and the assembly of a global norm are separate results;
this statement does not assert either of them.
