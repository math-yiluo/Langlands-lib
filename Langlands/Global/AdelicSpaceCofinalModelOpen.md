# Lifts and openness at cofinal principal model levels

Author: Worker 109.

This internal specialization combines `AdelicSpaceIntegerBase` with
`AdelicSpaceUniformModelOpen`. It discharges the latter's lifted-integer
algebra and integer-base local finite-type premises at the actual published
cofinal principal levels, in both global-field characteristics. Its
provenance is this direct composition of existing constructions; no new
external theorem is claimed as proved.

Given any finite initial place set `S`, write `T` for the
literal value of `curvePlacePrincipalLevelAbove k F S` or
`numberFieldPrincipalLevelAbove K S`. These published constructions return
an actual finite set containing `S`, and the literal ring of `T`-integers
is finite type over the original integers. All fields and spaces retain
arbitrary universe `u`. The curve-place section uses a finite constant
field and the given global function-field presentation.

The two `...CofinalSpacePointLifts_of_uniformLangWeil` definitions take
actual models over this ring and a morphism between them. Their remaining
premises are exactly the uniform space Lang–Weil statement, target
quasi-separatedness and `FiniteTypeOverRing`, a scheme chart with
surjective etale source and smooth map of one fixed relative dimension,
and separatedness, quasi-compactness, surjectivity and geometrically
connected fibres of the original model morphism. They return a finite
exceptional set in the full level factor index and an actual source point
above every original-coefficient target point outside it, with its exact
fibre equation. The number-field index includes all infinite places.

The two `...CofinalSpaceLevel_isOpenMap_of_uniformLangWeil` theorems instead
assume both models separated and `FiniteTypeOverRing`, together with the
same uniform-estimate and morphism-chart premises. They prove openness for
the actual `curvePlaceSpaceLevelTopology` or
`numberFieldSpaceLevelTopology`. The function-field openness theorem
requires the initial `S` nonempty. The chosen level contains `S`, so it
is nonempty as required by the existing model-level theorem. The lift
definitions do not need this nonemptiness premise.

Each proof installs the canonical `AdelicSpaceIntegerBase.algebra` on the
actual coefficient ring. Its finite-type instance over the integers
supplies `AdelicSpaceIntegerBase.locallyOfFiniteType`, after which the
corresponding original-base model theorem applies directly. No arbitrary
outside-set integer ring is asserted finite type.

These results apply to models already given over the chosen cofinal
levels. They do not produce a model by spreading an arbitrary generic
morphism, handle varying fibre dimensions, prove the uniform estimate,
or assemble open stage maps into an adelic map independent of the
original models. The unconditional
`AdelicSpaceSpreadSmoothOpenStatement` remains a separate obligation.
