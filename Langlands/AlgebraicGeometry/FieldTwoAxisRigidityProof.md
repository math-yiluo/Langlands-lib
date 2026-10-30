# Two-axis rigidity over arbitrary fields

Worker 423 implemented this assembly. Worker 334 supplied the square
reduction and faithful base-change route, demonstrated in his unaccepted
`FieldRigidityAssembly` revision 4. Worker 337 specified the general
scheme-map interface used by the published target. These are the actual
contributing workers.

The theorem `Langlands.AlgebraicGeometry.fieldTwoAxisRigidity.{u}` has exact
type `Langlands.AlgebraicGeometry.FieldTwoAxisRigidityStatement.{u}` for
every universe `u`. It imports the published statement unchanged. Its
quantified data are an arbitrary field, two smooth proper geometrically
connected pointed schemes, a separated locally finite type pointed target,
and a morphism from the product that is constant with the same value on both
axes. It proves equality with the constant morphism in the slice category,
including the full scheme morphisms and their structure-sheaf maps.

The assembly imports the published proofs
`Langlands.AbelianScheme.algebraicallyClosedTwoAxisRigidity` from
`Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidityProof` and
`Langlands.AbelianScheme.smoothGeometricIntegrality` from
`Langlands.AbelianScheme.SmoothGeometricIntegralityProof`.
Worker 416 implemented the latter assembly; its paired documentation
attributes the underlying smooth-domain-stalk and connected-domain-stalk
integrality proofs. The former proof is by Worker 423 with Worker 334's
contribution. No field or arbitrary-base pointed-group-morphism rigidity
theorem enters the dependency route.

The private helper `algebraicallyClosedTensor` starts over an algebraically
closed field and forms `A = Y ⊗ Z`, with section `a = (y₀,z₀)`. Here the
cartesian monoidal tensor in the slice category is the scheme fibre product.
Smoothness and properness are stable under fibre products. Geometric
connectedness follows by composing the geometrically connected projection
with a factor's structure map. The published theorem
`smoothGeometricIntegrality` applies to `A`. Mathlib gives integrality and
local Noetherianity of `A`, and then integrality of `A ⊗ A` over the
algebraically closed field.
Define `h((y₁,z₁),(y₂,z₂)) = g(y₁,z₂)`. Both axes of `h` factor through the
given axes of `g`; these identities are proved by comparing the product
projections. The published theorem `algebraicallyClosedTwoAxisRigidity`
makes `h` constant. Precomposition with the diagonal `A → A ⊗ A` recovers
`g`.

The private helper `fieldTensor` uses actual base change along
`Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))`.
All eight scheme-morphism properties on the factors and target are stable
under this base change. If `F` denotes its slice pullback functor, a section
`s` becomes `ε F ≫ F.map s`; the product map becomes
`μ F Y Z ≫ F.map g`. The strong monoidal product and terminal comparisons,
including `Functor.Monoidal.lift_μ` and `Functor.Monoidal.toUnit_ε`,
transport both axis equations. The algebraically closed helper therefore
gives equality of the pulled-back morphisms. Cancellation of the product
comparison isomorphism and faithfulness of this actual pullback functor
give equality over `K`. The faithful instance comes from Mathlib's
`AlgebraicGeometry.Morphisms.FlatDescent`: this field-extension morphism is
flat, surjective and quasi-compact. No separability condition is imposed.

The final declaration explicitly compares the two products used by the
target and the helpers. The comparison `e : Y ⊗ Z ≅ Y ⨯ Z` has forward map
`prod.lift (fst Y Z) (snd Y Z)` and inverse the cartesian monoidal lift of
the two `Limits.prod` projections. Both inverse identities follow by
projection extensionality. The tensor unit is the slice object
`Over.mk (𝟙 S)`, and uniqueness identifies its terminal arrows with
`Over.mkIdTerminal.from`. Both original axis equations transport through
`e`; applying `fieldTensor` to `e.hom ≫ g` and precomposing with `e.inv`
proves the exact target conclusion.

This is an internal derived proof of the unchanged published statement;
its original-source scope is documented in
`Langlands/AlgebraicGeometry/FieldTwoAxisRigidityStatement.md`. That companion
records the corrected Lan and GIT rigidity formulations and the EGM
variety-level context. The implemented proof uses the published square and
geometric-integrality theorems and Mathlib's categorical and scheme APIs.
It introduces no group object, properness or quasi-compactness hypothesis
on the target, extra field hypothesis, or additional rigidity, integrality,
global-functions or descent premise. Properness of both source factors is
used to make `A` proper for the square theorem.
