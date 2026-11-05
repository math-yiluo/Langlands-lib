# Changing the coefficient ring of actual integral models

This is an internal construction for arithmetic spreading, derived from the
published actual-pullback functor and its composition comparison. It introduces
no new geometric descent assumption. The construction works uniformly in the
scheme and coefficient-ring universe `u`.

The imported `Descent.pullbackComparison b a c h G` compares the successive pullbacks of `G`
along `b` and `a` with the pullback along `c`, where the supplied equality is
`h : a ≫ b = c`. Its first factor is the inverse of
`GroupScheme.baseChangeCompIso b a G`; its second factor transports along `h`.
`Descent.pullbackComparison_naturality` proves compatibility with every supplied
group-scheme homomorphism. The proof substitutes the composite map and uses the
naturality of the lifted pullback-composition natural isomorphism.

For domains `R` and `A` with the same fraction field `K`,
`M.baseChangeModel b hb` changes an actual `IntegralModel R K G` to an
`IntegralModel A K G`. Here `b : Spec A ⟶ Spec R` is an actual scheme map and
`hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K` fixes its relation to the
canonical generic inclusions. Its group is the actual pullback of `M.group`.
The affine, flat and locally finite type structural properties persist by base
change. Its generic identification is the composition comparison followed by
`M.genericIso`; it therefore identifies the new generic fibre with the same
supplied group `G`. `smooth_baseChangeModel` proves that smoothness of the
structural map persists as well.

For an existing model homomorphism `φ : M.Hom N f`, `φ.baseChange b hb` pulls
back its actual homomorphism. The generic compatibility equality follows from
comparison naturality and `φ.generic_comm` by associativity. Finally,
`Hom.isClosedImmersion_baseChange` proves that a closed immersion remains a
closed immersion. Its proof constructs the Cartesian square for the underlying
pulled-back map by cancellation of the two structural pullback squares, then
uses stability of closed immersions under base change.

The naturality argument was developed from Worker 1596's shared `FieldFibers`
draft. The Cartesian-square argument follows the published internal construction
`SchematicImageComparison.isSchemeTheoreticallyDominant_baseChange`, with the
closed-immersion morphism property in place of schematic dominance. All other
ingredients are the imported category-theoretic pullback and morphism-property
lemmas. This unit supplies transport of existing models and homomorphisms;
existence of an extending homomorphism and the reductive and parabolic fibre
conditions remain separate obligations of the full spreading theorem.
