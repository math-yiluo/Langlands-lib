# Compatible sections of a scheme solution along fppf covers

This module is the fppf analogue of the étale part of the published module
`Langlands.GroupScheme.Descent.SchemeSolutionSections`. All schemes lie in an
arbitrary universe `u`. Let `p : S ⟶ B` be surjective, flat and locally of
finite presentation, `D : Datum p G` a Čech datum for an actual group scheme
`G` over `S`, and `s : SchemeSolution D`. The published module defines the
subgroup `sectionSubgroup (D := D) U` of compatible local sections over
`U : Over B`, and the restriction `s.localSection`. Neither definition needs a
hypothesis on `p`.

- `fppfLocalSection_injective`: restriction of sections `U ⟶ s.obj` is
  injective. Slice pullback along `p` is faithful (Mathlib instance for
  surjective flat maps locally of finite presentation,
  `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`), and `s.iso.hom` is a
  monomorphism.
- For a compatible section `x`, the map `x.val.left ≫ s.proj` takes equal
  values on any two test points above the same point of `U`. This is the
  private lemma `fppfInvariant_section`, which uses the published
  `sectionTransport_eq_iff`. The projection `p*U ⟶ U` is a base change of `p`,
  so it is again an fppf surjection and hence an effective epimorphism. This
  descends `x.val.left ≫ s.proj` to a map `U.left ⟶ s.obj.left`. Cancelling the
  epimorphism shows that this map lies over `B`, which gives
  `fppfSectionDesc x : U ⟶ s.obj`.
- `localSection_fppfSectionDesc`: restriction recovers `x`. The proof applies
  the supplied pullback square of `s`.
- `fppfSectionEquiv U : (U ⟶ s.obj) ≃ sectionSubgroup (D := D) U` is the
  resulting bijection.

No affineness, quasi-compactness, field, smoothness or finite-type hypothesis
is used. Provenance is internal: the proofs repeat the published étale
arguments with Mathlib's fppf effective-epimorphism and faithfulness
instances.
