# Proper Hom representation from explicit geometric inputs

This internal reduction constructs an actual affine, locally finitely presented
scheme representation of the full actual-family Hom presheaf, **assuming**
the two exact propositions `NoetherianHomFiniteLinearModelsStatement` and
`Modules.ProperAffineNoetherianModelExistenceStatement`. Both are explicit
arguments of the construction. This module proves neither geometric input
and does not provide an unconditional proof of
`ProperHomRepresentabilityStatement`.

The entry definition `properHomRepresentationOfGeometricInputs` returns a
scheme over the test base, a natural isomorphism of its lifted functor of
points with `FamilyGroupoid.homPresheaf`, and proofs that the same structure
map is affine and locally of finite presentation. It works for every universe,
every proper locally finitely presented ambient morphism, every test scheme,
and the actual flat finitely presented module families of the existing
`FamilyGroupoid`. All tests and all module morphisms are retained.

The implemented proof has four steps:

1. `intrinsicHom_representable_noetherian` applies the first geometric premise
   over a noetherian affine base. Finite presentation of the target supplies
   quasi-coherence, so actual intrinsic Hom is an fppf sheaf. The theorem
   `FiniteLinearEquations.HasLocalModels.exists_affine_representation` glues
   the finite linear models to an affine locally finitely presented
   representative on the full slice.
2. `intrinsicHom_representable_affine` unpacks the second geometric premise.
   The model includes an actual Cartesian square, finite presentations,
   target relative flatness, and ordinary module-pullback isomorphisms.
   Step 1 represents the model Hom presheaf. The representation is pulled
   back along the spectrum of the model ring map; affineness and local finite
   presentation survive this base change. The natural isomorphism
   `intrinsicModuleHomCartesianOfIso` then transfers it to the given modules.
3. `intrinsicHom_representable` uses the affine open cover of an arbitrary
   base. Properness, local finite presentation, finite presentation of both
   modules, and relative flatness of the target survive ordinary pullback.
   Step 2 represents the intrinsic Hom presheaf on every chart.
   `intrinsicModuleHomBaseChangeIso` identifies it with restriction of the
   original presheaf. Full-slice gluing, using its fppf sheaf property,
   produces a global scheme representative and both structure-map properties.
4. `properHomRepresentability_of_geometricInputs` applies step 3 to the actual
   relative projection of the ambient morphism and the underlying modules of
   the two actual families. It transports the result along
   `FamilyGroupoid.homPresheafIntrinsicIso`, proving the exact target
   proposition conditionally on the two inputs. The entry definition chooses
   the data supplied by this existential theorem.

The reduction is derived by composition of the existing definitions,
pullback comparisons, Hom descent, local representation gluing and standard
stability of morphism properties. It asserts no additional source theorem.
The noetherian finite-equation and approximation arguments remain obligations
of the two input statements and are not replaced by weaker geometric
hypotheses or by assumed representation data.
