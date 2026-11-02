# Invariance of the finite locus

`FiniteLocusInvariantProp` states that the largest open `W` over which `s` is
finite is invariant under an étale equivalence relation `t,s : R → U` with
`s` separated: `s⁻¹W = t⁻¹W`. The theorem `finiteLocus_invariant` proves this
proposition for every universe. It requires no quasi-compactness, affine,
Noetherian, or finite-type hypotheses beyond the stated étaleness.

This is an internal derivation from `AtlasRelation.IsEquivRel`, the actual
maximal finite locus in `FiniteLocus`, and Mathlib scheme morphism properties.
The equivalence relation is a monomorphism into the product and is reflexive,
symmetric, and transitive on every scheme-valued test object.

The proof is implemented as follows.

1. `IsEquivRel.hom_ext` derives uniqueness of arrows into the relation from
   their two projections, using the product monomorphism.
2. `IsEquivRel.exists_isPullback_composition` constructs composition on
   `R ×_{s,U,t∘e} E` for any `e : E → R`. The composition and projection to
   `E` also form a pullback of `s` along `s∘e`. Composition and inversion in
   the relation give existence of lifts; the preceding uniqueness gives the
   universal property.
3. The `saturation` of an open `W` is the actual open image `t(s⁻¹W)`.
   It is open since the composite of the open inclusion with `t` is étale.
   If `s` is finite over `W`, then `finite_composition_baseChange` uses the
   composition pullback square and the restriction square to show that
   `R ×_{s,U,t} s⁻¹W → s⁻¹W` is finite.
4. `isFinite_restrict_saturation` factors `s⁻¹W → U` through the saturation.
   This factor is étale, since its composite with the open inclusion is
   étale, and it is surjective by the definition as an image. The pullback
   of `s` restricted to the saturation along this cover is the finite map
   from step 3. Universal closedness descends along this surjective flat
   morphism locally of finite presentation, by Mathlib fpqc-to-fppf
   descent. The restricted `s` is also separated and locally of finite
   type, hence proper. It is locally quasi-finite by
   `GenericFiniteness.locallyQuasiFinite_of_etale`, so Mathlib's proper
   locally quasi-finite criterion gives finiteness.
5. `invariant_of_maximal` applies maximality to put the saturation inside
   `W`, giving `s⁻¹W ⊆ t⁻¹W`. The involution of the relation gives the
   reverse inclusion. Finally, `finiteLocus_invariant` uses the actual
   finiteness and maximality of `finiteLocus s`.

The imported `GenericFiniteness` module contains the separately attributed
adapted result providing local quasi-finiteness of étale maps. This module
adds the internal relation and descent argument, and does not itself prove
the dense affine open statement or the host group-space representability
statement.
