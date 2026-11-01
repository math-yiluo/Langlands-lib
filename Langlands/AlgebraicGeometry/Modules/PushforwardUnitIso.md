# The structure-module pushforward comparison

This internal adapter converts the published theorem on all open-section
maps into an actual isomorphism of module sheaves.

For a map `p : X → S`, `isIso_unitToPushforwardUnit_of_isIso_app`
assumes that `p.app U` is invertible for every open `U` of `S`.
It proves invertibility of the published
`Langlands.Scheme.Modules.unitToPushforwardUnit p`, the canonical map
`O_S → p_* O_X`. Here `O_X` is exactly
`SheafOfModules.unit X.ringCatSheaf`; the direct image is Mathlib's
`Scheme.Modules.pushforward p`.

On each open, the module map has exactly the same underlying function as
`p.app U`. An isomorphism of rings gives a bijection of these functions,
hence an isomorphism of modules. The proof uses
`PresheafOfModules.isoMk` to assemble the component inverses; naturality
of the forward maps is inherited from the canonical comparison.
The fully faithful forgetful functor from module sheaves to module
presheaves reflects isomorphisms, giving the asserted result for sheaves.

`isIso_unitToPushforwardUnit` applies this criterion to any smooth proper
morphism with geometrically connected fibres, using the independently
published
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`.
`pushforwardUnitIso p` packages the result as an actual isomorphism.
`pushforwardUnitIso_hom` identifies its forward map with the canonical
comparison by reflexivity.

The construction is derived from the existing Library interfaces
`PullbackUnit` and `SmoothProperConnectedGlobalFunctionsProof` and
Mathlib's presheaves and sheaves of modules, pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`. It introduces no new
literature assertion. The hypotheses and universe are those of the
published smooth proper global-functions theorem. No valuation, finite
type or Noetherian hypothesis on `S` is imposed. The comparison supplies
neither correspondence representability nor extension of line bundles.
