# Construction of smooth and flat filtered-ring models

This proof targets `SchemeFilteredSmoothFlatModelExistence`, using the
unchanged proposition pair `SchemeFilteredPropertyModelStatement`.
It proves existence of property-bearing structural models at actual
original ring stages, retaining nonaffine and nonseparated schemes and
arbitrary transition maps.

The exact theorem is
`Langlands.AlgebraicGeometry.SchemeLimitModel.schemeFilteredSmoothFlatModelExistence :
SchemeFilteredSmoothFlatModelExistence.{u}` for arbitrary universe `u`.
The construction and proof were written by Worker 105 in the shared
task draft; Worker 1572 reused that proof unchanged and checked it against
the published target and its Library dependencies.

The target is an internal derivation from Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 3.4(1)–(2),
printed pp. 5–6. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof below takes a noetherian approximation route rather than
assuming the eventual-property assertion of that theorem.

The private helper `propertyModelExistence` uses a property stable under
base change and a subalgebra-descent theorem over noetherian coefficient
rings. It first applies the published
`NoetherianApproximation.schemeSubalgebraDescent` over `ULift ℤ`. The
resulting coefficient subalgebra `T₀` is finitely generated over lifted
integers, hence noetherian. The actual pullback square identifies the
given structural morphism with the canonical pullback of the resulting
model; invariance under isomorphisms transfers the property to that
canonical pullback.

Subalgebra descent produces a finitely generated `T₀`-subalgebra `T₁`
with the desired property. The new model is the canonical pullback to
`Spec T₁`. Composition of the scalar-tower algebra maps gives the exact
composite spectrum map, and cancellation of the right pullback square
gives an actual pullback comparison with the original scheme.

The tower makes `T₁` finitely generated over lifted integers and thus
finitely presented over that noetherian base. The spectrum map from the
original colimit ring to `Spec T₁` factors through one of the actual
spectra of the original ring diagram by
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`. Pulling
the `T₁` model back to that stage preserves the property, local finite
presentation, quasi-compactness and quasi-separatedness. A second
pullback cancellation gives the claimed square with the original
ring-cocone map.

The concrete smooth proof supplies the published
`NoetherianApproximation.smoothSubalgebraDescent`. The flat proof supplies
the published port
`AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd`.
Both ports originate in the Anthropic FLT development, as documented
in their own paired provenance and license files, and are imported
without modifying or reproducing their proofs. Their application
discharges the private helper's descent hypothesis in each case.

The combined theorem is the conjunction of these two concrete proofs.
This implemented route is an internal derivation for the Conrad
prerequisites; it does not prove eventual properties of a prescribed
model or the full relative property-descent clauses.
