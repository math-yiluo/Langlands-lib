# Left homogeneous quotients and positive right translation

This internal construction supplies the carrier and topology needed for the
general reductive adelic quotient. It applies to every group `H : Type u` and
every subgroup `Γ`, with no normality assumption. It does not yet identify any
particular rational or split-centre subgroup.

`Langlands.Global.LeftCosetSpace Γ` is the actual orbit quotient
`Quotient (QuotientGroup.rightRel Γ)`, hence represents `Γ \ H`.
The carrier, projection, positive translation, invariant-function descent,
translation homeomorphism and topology results reuse the existing declarations
in [Group/LeftQuotient](../Group/LeftQuotient.md). `LeftCosetSpace.mk` is
the quotient projection. The equality criterion is
`mk Γ x = mk Γ y ↔ y * x⁻¹ ∈ Γ`, and `mk_subgroup_mul` identifies representatives
related by multiplication on the left by an element of `Γ`.

`rightTranslate Γ g` sends the class of `x` to the class of `x * g`.
Its construction checks the defining relation by cancellation. The composition
law is

\[
 T_h(T_g(q))=T_{gh}(q).
\]

Consequently points have a left action of `Hᵐᵒᵖ`.
`rightRegularAction Γ E` supplies the positive left action of `H` on
quotient-valued functions, with
`R(g)f(q) = f(T_g(q))`. This action is a named structure rather than a global
instance on function types, avoiding a collision with pointwise coefficient
actions. The codomain `E : Type v` is arbitrary.

`lift` descends a function `f : H → E` with
`f (γ * x) = f x` for every `γ : Γ`.
`functionEquiv` gives the actual equivalence between quotient functions and
these invariant functions. Quotient induction proves the inverse laws.

For a topological `H`, the quotient inherits the quotient topology.
`continuous_mk`, `isQuotientMap_mk`, `continuous_iff` and `continuous_lift`
give its universal property. When `H` is a topological group,
`invHomeomorph` sends the class of `x` to the class of `x⁻¹` in Mathlib's
`H ⧸ Γ`, whose representatives are the cosets `x Γ`.
Both directions are continuous by the quotient universal property and
continuity of inversion.

The projection is open because it is the orbit projection for the continuous
left `Γ` action. `rightTranslateHomeomorph` has inverse right translation by
`g⁻¹`. The opposite-group action is jointly continuous, proved by descent from
the product of the identity and the open quotient projection. The quotient is
locally compact when `H` is locally compact, second countable when `H` is second
countable, and Hausdorff when `Γ` is closed. The last assertion uses the proper
action of a closed subgroup on a topological group.

The provenance is internal: the definitions and proofs specialize pinned
Mathlib's coset, orbit-quotient, open-quotient and proper-action APIs, notably
`GroupTheory/Coset/Defs.lean`, `Topology/Algebra/ConstMulAction.lean`,
`Topology/Algebra/Group/Quotient.lean` and
`Topology/Algebra/ProperAction/Basic.lean`. The representative formulas prove
the convention explicitly. Measures, discrete subgroup existence, adelic point
topologies, the split-centre comparison and finite volume remain separate
constructions and assertions.
