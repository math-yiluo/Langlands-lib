# Separated models of algebraic spaces over rings of `S`-integers

Author: Worker 208.

This helper module proves the existence clauses of
`Langlands.Global.CurvePlaceSpaceSpreadStatement` and
`Langlands.Global.NumberFieldSpaceSpreadStatement`, from
`AdelicSpacePointTopologyStatement`. Every separated algebraic space of finite
type over a global field `F` has a separated model of finite type over the ring
of `S`-integers for some `S`, together with an isomorphism from its generic
fibre to the given space. In the function-field case `S` is nonempty, as the
statement requires. The source is Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (31 December 2011), printed p.17, which uses such
models to topologize `X(A_F)`; registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The
independence clauses of the two statements are separate results.

## Declarations

- `finitePresentationAtlas_of_finiteTypeOverRing`: over a field, an atlas that
  is locally of finite type and quasi-compact is locally of finite presentation.
  The atlas scheme is locally Noetherian, by
  `LocallyOfFiniteType.isLocallyNoetherian`, and Mathlib then gives local finite
  presentation.
- `finiteTypeOverRing_of_atlas`: a quasi-compact, locally finitely presented
  atlas is locally of finite type (`HasAtlasProperty.mono`).
- `curvePlaceSpaceSpreadExistence`. Choose a place `v` with
  `curvePlace_nonempty`, and set `S₀ = {v}`. The Library's integer-ring diagram
  `curvePlaceSIntegersOverDiagram k F S₀` has colimit the function field, by
  `curvePlaceSIntegersOverIsColimit`. Its diagram of spectra
  (`spectrumDiagram`, `spectrumCone`, `spectrumConeIsLimit`) is a cofiltered
  diagram of affine schemes with limit `Spec F`. `spaceLimitModelExistence`
  then gives a stage `T ⊇ S₀` and a separated model over the `T`-integers
  whose base change along the spectrum of the inclusion is isomorphic to the
  given space. That base change is by definition the generic fibre
  `curvePlaceSpaceGenericFiber`. Since `T` contains `v`, it is nonempty.
- `numberFieldSpaceSpreadExistence`: the same argument with the number-field
  diagram `numberFieldSIntegersOverDiagram K ∅` and
  `numberFieldSIntegersOverIsColimit`.
