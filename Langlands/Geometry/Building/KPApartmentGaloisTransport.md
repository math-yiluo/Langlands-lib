# Coefficient covariance and split-torus compatibility

This module derives covariance of actual character evaluation and preservation
of the existing split-torus compatibility predicate under coefficient
automorphisms. It is an internal consequence of the published descent,
character-lattice, rational-point and root-function constructions. It introduces
no original-source assertion, existence assumption or replacement predicate.

Fix fields `k` and `K` in an arbitrary universe `u`, an algebra `k → K`, and
a commutative group scheme `T` over `k`. Write `T_K` for its scalar extension
along `algebraBaseMap k K`. No finite-extension, separability, completeness,
valuation, splitness or reductivity hypothesis is needed for evaluation
covariance.

For every `σ : K ≃ₐ[k] K`, every actual character `a` of `T_K`, and every
`K`-point `s` of `T_K`,
`GaloisPointComparison.rationalCharacterEval_galois` proves that evaluation of
`characterLattice.galoisRepresentation k K T σ a` at
`rationalConjugate k K T.toGrp σ s` is `Units.map σ.toMonoidHom` applied to
the original evaluation. The character is arbitrary upstairs; it need not
descend to `k`.

The proof first uses `characterLattice.galoisRepresentation_points` and
`descentPoint_rationalConjugate`. The generic helper
`characterLattice.points_of_descent_eq` turns their composite into a
pullback of global units, using `Gm.pointsEquiv_naturality`. The lemma
`rationalCharacterEval_lattice` expresses rational character evaluation through
these global units. `units_ΓSpecIso_naturality` then identifies their pullback
with the coefficient automorphism on `Kˣ`. The latter lemma follows from
`Scheme.ΓSpecIso_naturality` by extensionality of units.

For an arbitrary function `ω : Kˣ → ℝ` invariant under this one `σ`,
`GaloisPointComparison.rationalCharacterOmegaEval_galois` applies `ω` to
the covariance equality and removes the coefficient automorphism. No additivity
or valuation law is required of `ω`. The elementary
`invariant_apply_of_inverse` and `units_map_algEquiv_inv` show that invariance
under `σ` also implies invariance under its inverse.

For group schemes `G` and `H` descended from `k`,
`GaloisPointComparison.rationalConjugate_map` proves naturality of the actual
coefficient action under the scalar extension of any map `G ⟶ H`. Its proof
uses injectivity of `baseChangeCoeffEquiv`, its action and map comparison laws,
and naturality of affine points. It imposes no affine hypothesis on `G` or `H`.

For `i : T.toGrp ⟶ G` with affine structural morphism of `G`, and the
scalar-extended map `i_K`, the main result
`IsSplitTorusCompatible.galoisTransport` states that if a family `φ` satisfies
the existing `IsSplitTorusCompatible i_K ω φ`, then
`RootFunctionFamily.galoisAction k K T G σ φ` satisfies the same predicate,
provided `ω` is invariant under `σ`. Neither a monomorphism hypothesis on `i`
nor a Galois stability premise on a chosen class is used.

The generic `IsSplitTorusCompatible.pullbackTransport` pulls the defining conjugation
identity back along supplied character, ambient-point and torus-point maps.
It assumes exactly preservation of roots, preservation of root groups,
naturality of the torus map, the family pullback identity and preservation of
`ω` applied to character evaluation. Multiplicativity of the ambient-point
map then transports the conjugation expression.

The coefficient specialization first proves
`IsSplitTorusCompatible.galoisTransport_inv`. The elementary
`RootFunctionFamily.galoisAction_inv_apply` identifies the inverse family
action with pullback along the forward character and point maps. Root and
root-group covariance supply the membership hypotheses, naturality supplies
the map identity, and the invariant evaluation result supplies the last
condition. Applying this inverse-action result to `σ⁻¹` and simplifying
`σ⁻¹⁻¹ = σ` gives the main result.

The definition `IsSplitTorusCompatible.galoisEquiv` restricts the original
coefficient permutation to the subtype of exactly all split-torus-compatible
families. Its forward and inverse maps are the original family actions of `σ`
and `σ⁻¹`; their membership proofs are the two transport results. The inverse
laws follow from the existing family action's group laws and subtype
extensionality. `galoisEquiv_val` records that the underlying family is
unchanged by this restriction. No inhabitant of the subtype is assumed.

This proves transport of the split-torus portion of V6 for a supplied family.
It does not construct a valuation, a compatible equipollence class or a
canonical apartment, and it does not assert stability of any selected class
or full centralizer compatibility. Those are further obligations in the
building comparison construction.
