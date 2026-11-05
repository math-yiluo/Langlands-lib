# Recovering actual fibre inclusions from Hom parameters

These internal helpers compare the actual evaluation interface in
`HomScheme.Universal` with the raw base-change morphisms used in fibre
inclusion squares. They require no representability or lifting theorem.

`evaluate_comparison` states that raw base change of a homomorphism,
followed by the target pullback comparison, equals the source pullback
comparison followed by evaluation. The proof unfolds `evaluate` and
`Descent.pullHom` and cancels the inverse source comparison.

`isClosedImmersion_evaluate_iff` transports closed immersion in both
directions through those actual source and target isomorphisms. Its
proof writes each map as the other map composed with the two comparisons
and applies stability of closed immersions under composition with
isomorphisms.

`recover_fibre_inclusion` applies to any schemes `K`, `U`, and `S`, maps
`p : U ⟶ S`, `c : K ⟶ S`, and `b : K ⟶ U` with `b ≫ p = c`.
Given an actual source-fibre isomorphism `e₀ : H_K ≅ T₀`, an inclusion
`i₀ : T₀ ⟶ G_K`, and a family `i : H_U ⟶ G_U` whose evaluation at `b`
is exactly `e₀.hom ≫ i₀`, it constructs the actual iterated-fibre
isomorphism `fibreComparisonIso` and proves the full inclusion square. The displayed
ambient comparison is exactly `(baseChangeCompIso p b G).inv`
followed by the isomorphism induced by the supplied base-map equality.
The source isomorphism composes the corresponding source comparison
with `e₀`.

## Provenance and limits

The construction is derived internally from the published
`Descent.pullbackComparison` and `Descent.pullHom` definitions and the
actual Hom evaluation construction. The final proof substitutes the
given evaluation equality into `evaluate_comparison` and unfolds the
comparison isomorphisms. It does not infer equality merely from
abstract isomorphism of fibre groups.

These lemmas perform categorical transport. They do not produce a
parameter, an etale neighbourhood, a torus, or a closed inclusion.
Those existence assertions remain separate proof obligations in
pointed split-torus lifting.
