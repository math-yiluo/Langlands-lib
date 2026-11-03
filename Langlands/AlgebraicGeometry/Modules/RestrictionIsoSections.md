# Section transport for restriction isomorphisms

Let `S` be an arbitrary scheme, let `M` and `N` be module sheaves on `S`,
and let `U` be an open. An actual isomorphism
`f : M.restrict U.ι ≅ N.restrict U.ι` gives an isomorphism
`overRestrictionIso f : M.over U ≅ N.over U` on the slice of original
opens contained in `U`.

The construction conjugates `f` by the two canonical components of
`Scheme.Modules.overFunctorEquiv U`, then takes its preimage under the
fully faithful functor of `Scheme.Modules.overEquiv U`. The lemmas
`overRestrictionIso_refl`, `overRestrictionIso_symm` and
`overRestrictionIso_trans` prove preservation of identity, inverse and
composition. Their proofs use faithfulness, the preimage equation, and
cancellation of the comparison isomorphisms.

For every original open `V ≤ U` and every section `x : Γ(M,V)`,
`overRestrictionIso_hom_app` identifies the component on the slice object
`Over.mk (homOfLE h)` with `SerreVanishing.modE f V h x`. Thus this component
is the actual section transport on the original open, with the same
restriction and scalar compatibility already proved for `modE` in
`Modules/SerreVanishing/ChartOf.lean`.

To prove the component formula, the implementation maps the preimage
isomorphism forward through `overEquiv`, evaluates its homomorphism on
`U.ι ⁻¹ᵁ V`, and views the result as a section over
`U.ι ''ᵁ (U.ι ⁻¹ᵁ V)`. Naturality of the slice morphism then compares
this section with its component on `V`. The two restriction maps in
opposite directions compose to the identity, since `V ≤ U`.

This is derived infrastructure from the published open-restriction,
slice-equivalence and `modE` constructions; it asserts no external
literature theorem and assumes no local freeness or finiteness. It supplies
a section-level bridge for local frame comparisons. Tensor-frame
transition formulas, tensor-line projective invariance, and the host
`LargeLevelRepresentabilityStatement` remain separate obligations.
