# Properness along actual filtered ring and affine scheme limits

This unit records the properness clause of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2), and derived model-existence and relative forms.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
All sizes share arbitrary universe `u`. The Lean file defines propositions.

`ProperDescent` conjoins six concrete assertions:

- `SchemeFilteredProperModelExistence`: a finitely presented proper scheme
  over the actual colimit of a small filtered ring diagram has a finitely
  presented proper model over an actual original stage, with an actual
  Cartesian square identifying its given structure morphism after base change.
- `InitialRingModelProperDescent`: a prescribed finitely presented model
  over an initial ring is proper at the colimit exactly when its actual
  pullback along an original arrow out of the initial stage is proper.
- `RelativeProperDescent`: for a small cofiltered diagram of affine schemes
  over an affine base, an actual limit cone and compatible base map, a
  relative morphism that is locally of finite presentation, quasi-compact
  and quasi-separated, whose relative target is quasi-compact over the base,
  becomes proper at the limit exactly when its actual base change to some
  original stage is proper.
- `SpectrumProperDescent`: the preceding relative equivalence for the
  actual spectra of a filtered algebra diagram and its actual colimit.
- `InitialRingProperDescent`: the relative equivalence using precisely
  `Spec.map (c.ι.app j₀)` and `Spec.map (F.map j.hom)` for an actual
  `j : Under j₀`. It has the same relative finiteness hypotheses.
- `FinitePresentationInitialRingProperDescent`: the source properness clause
  for two arbitrary models locally of finite presentation, quasi-compact
  and quasi-separated over an initial ring. These model hypotheses imply
  the relative hypotheses; they are not assumed again on the morphism.

The first two assertions instantiate `SchemeFilteredPropertyModelExistence`
and `InitialRingModelPropertyDescent` at `IsProper`. The third instantiates
`RelativePropertyDescent`. The last three instantiate the corresponding
relative original-ring forms. Their defining modules describe the exact
maps and all finiteness hypotheses. No separatedness is imposed on the
initial models, nor are the models required to be affine. Ring transitions
may be noninjective. For directed posets, the under-category stage is
exactly an eventual stage greater than or equal to the initial stage.

The proof first uses noetherian approximation over lifted integers. It
then descends separatedness to a finitely generated subalgebra before
applying the published properness subalgebra theorem. Actual finite
presentation factors the resulting model through an original ring stage.
Isomorphism descent compares this proper model to a prescribed model.
Affine target charts and finite-cover gathering give relative descent.
Finally, actual spectrum limits and the initial-stage algebra tail give
both ring forms; finite-presentation cancellation gives the source form.
These are derived supporting results and the source's properness clause,
not the other properties or whole-paper coverage.
