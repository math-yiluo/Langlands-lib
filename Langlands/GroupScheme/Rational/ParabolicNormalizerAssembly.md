# Conditional assembly of all-test parabolic self-normalization

This internal assembly retains the exact published structural statements as
premises. It does not prove any of those premises or the unconditional
`ParabolicSelfNormalizerStatement`.

Any morphism between spectra of fields is the spectrum of its `Spec.preimage`
ring homomorphism. Giving its target the induced algebra structure permits
the exact field-extension statement to be applied to the actual base change,
without restricting the original scheme morphism.

The dynamic description of parabolics and preservation of connected reductivity
under field extension imply preservation of parabolics: base change the
cocharacter, use equality of dynamic parabolics under arbitrary base change, and
apply the reverse direction of the dynamic description. The exact dynamic
connectedness statement also proves connectedness of each parabolic source.
These implications still assume their structural premises.

The proved algebraically closed Borel-factorization adapter gives an actual
Borel inclusion and factor through each actual pulled-back parabolic inclusion.
Together with the preceding results, this gives the geometric Borel-overgroup
condition without a further factorization premise.
The open-cell lemma chooses a cocharacter representing the given inclusion, chooses
the published affine representative of its opposite dynamic unipotent, and
uses the exact opposite-cell statement. The proved dynamic separation lemma
eliminates that opposite factor in the all-test normalizer. The earlier
geometric Borel reduction then proves equality of the actual subgroup functors
on every test scheme. The geometric membership step uses Borel conjugacy and
Borel point normalization as explicit global premises.

This is derived content from the named Library interfaces. No structural
assertion is discharged by its name or by restating it as a hypothesis.

`parabolicSelfNormalizerStatement_of_structural_statements` has the exact existing
`ParabolicSelfNormalizerStatement.{u}` as its conclusion, conditional on these six
universe-polymorphic global propositions:

- `BorelConjugacyStatement` and `BorelNormalizerStatement`;
- `ParabolicDynamicStatement` and `OppositeCellStatement`;
- `DynamicConnectedStatement`;
- `ConnectedReductiveFieldExtensionStatement`.

All six remain proof obligations. This contribution supplies no unconditional
proof of the host target and does not weaken or edit that target.

The entry construction `normalizerPointsEquivOfStructuralStatements` specializes
the conditional equality to an arbitrary test scheme `T`, transports normalizer
points to range points, and applies the inverse of the represented-subgroup
point equivalence. It gives a multiplicative equivalence with actual morphisms
`T ⟶ P.X`. Its companion `_comp` theorem says that the returned morphism composed
with the original inclusion equals the original normalizer point. No affine or
reducedness assumption is imposed on `T`, and all results retain arbitrary
universe `u`.

Worker 1346 implemented this assembly. Worker 1297 supplied the actual
algebraically closed Borel-factorization adapter used to remove the earlier
factorization premise.
