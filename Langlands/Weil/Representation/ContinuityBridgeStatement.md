# Exact compatibility target

`Langlands.Weil.RepresentationContinuityCompatibility.{uG,uV}` is a proposition
definition with five conjuncts. It compares presentations; it does **not**
claim either universal continuity family as a theorem.

1. `CarrierTopologyComparison` says that any Hausdorff finite-dimensional complex
   topological vector space has exactly `moduleTopology ℂ V`. Its hypotheses are
   continuity of addition and negation, continuity of complex scalar
   multiplication, and Hausdorffness. Thus any two compatible norm topologies,
   or choices of finite coordinates used to construct them, give the same
   topology. There is no equality of norms claimed.
2. `EndomorphismTopologyComparison` identifies the canonical topology on
   `Module.End ℂ V` with the topology induced by
   `LinearMap.toContinuousLinearMap` from the usual operator topology on
   continuous linear maps. This is the actual bijection preserving the action
   on each vector, not an assumed homeomorphism.
3. `ChosenCarrierTopologyComparison` applies the concrete coordinate norm from
   `ContinuityBridgeDefinitions` to every bundled carrier and requires its
   topology to be canonical.
4. `RepresentationPredicateComparison` requires equality of the actual
   restricted representations, inertia kernels and ranges, followed by the
   continuity, orbit, joint-action, open-kernel and finite-image predicate
   comparisons in the interface table of `ContinuityBridgeDefinitions.md`.
   It also compares the complete five-clause expressions for one
   representation. These comparisons work for any subgroup of any topological
   group carrier; they do not need inertia to be compact or open.
5. The final conjunct is the equivalence of
   `BundledRepresentationContinuity` and the **unchanged**
   `RepresentationContinuity`. Both sides quantify over open, compact,
   nonarchimedean inertia and retain the closed-kernel condition in the
   finite-image converse. To pass from the unbundled family to an arbitrary
   bundled object, a proof must use the constructed norm and the topology
   comparison, not restrict the bundled quantifier to pre-existing normed
   objects.

The universes of group and carrier are independent. Every comparison includes
the zero-dimensional carrier. The complex field always carries its usual
topology.

The intended callable proof interface includes the individual predicate
comparisons, an endomorphism homeomorphism, a topology uniqueness lemma for two
compatible topologies, the constructed-carrier comparison, a pointwise
five-clause comparison and the family equivalence. The main proof must have
exact type `RepresentationContinuityCompatibility`; none of these targets is an
unproved assumption available to that proof.

Provenance is internal and derived from the published
`Langlands.Weil.Representation.Basic`, `Predicates`, and `Continuity` interfaces,
and the accompanying definition pair. Mathlib's
`isModuleTopologyOfFiniteDimensional` in
`Mathlib/Topology/Algebra/Module/FiniteDimension.lean` supplies the underlying
finite-dimensional topology theorem; `LinearMap.toContinuousLinearMap` supplies
the algebraic bijection. The version is
`5ed2965256430c3649e86755f9576b54eca72435`. No new statement from the original
Weil-group literature is attributed to this interface comparison.

Author: Worker 38.
