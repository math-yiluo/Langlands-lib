# Finite projective representatives for bounded flat complexes

`Langlands.Cohomology.ModuleComplex.BoundedFlatComplexProjectiveStatement.{u}`
is a Prop-valued statement about natural-number-indexed cochain complexes of
modules. It is a focused algebraic input to the noetherian part of universal
perfect sections.

Let R be a commutative noetherian ring and let C be a complex of flat R-modules,
all in an arbitrary universe u, with differential d increasing degree by one.
Assume C is zero in degrees strictly greater than a specified n, that ker(d 0)
is finite over R, and that each positive cohomology module
ker(d(i+1)) / im(d i) is finite over R. Here “zero” is represented by
`Subsingleton`, and the quotient in Lean uses the inverse image of the range
inside the kernel.

The statement asserts that there is a complex K of finite projective R-modules,
zero in degrees strictly greater than the same n, together with a chain map
φ from K to C inducing isomorphisms on all cohomology modules. The Lean conclusion
expresses this last assertion by four cycle and boundary conditions: injectivity
and surjectivity on degree-zero cycles, followed by injectivity modulo
boundaries and surjectivity modulo boundaries in every positive degree. The
quantified differential-square-zero and chain-map identities are explicit.
The proposition chooses K and its module structures before stating these
conditions. It asserts no uniqueness, functorial choice, or geometric comparison.

## Provenance

The theorem type is taken from the registered original
`anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
Anthropic FLT commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:

- `Theorems/Thm_Module_exists_projective_complex_quasiIso_of_flat_complex.lean`,
  complete theorem `Module.exists_projective_complex_quasiIso_of_flat_complex`;
- `P2M/Sol/S_Module_exists_projective_complex_quasiIso_of_flat_complex.lean`,
  theorem `solution` and the `MumfordModel` construction.

This file preserves the quantified theorem type and moves it under a
Prop-valued definition in the Langlands namespace. It imports Mathlib alone;
the original proof and P2M wrapper are not part of this statement. No proof
is claimed here. Copyright and license are retained in the Lean header and in
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
