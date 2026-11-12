# Proper maps on adelic coordinates and stages of algebraic spaces

This derived infrastructure follows the product argument for proper adelic maps in
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.11,
and its algebraic-space extension on printed pp.16–17. It uses the published actual
ring-point, coordinate-topology and stage constructions.

The helper `isProperMap_of_homeomorph` transports properness across a commuting
square of homeomorphisms by expressing the original map as a conjugate.
`fieldFactorPointHomeomorph` bundles the published field-valued point
identification for a bijective coefficient map as a homeomorphism, and
`isProperMap_fieldFactor` applies conjugation to it.

`continuous_factor` uses the defining induced topology and the published
functoriality of the étale-chart topology over a henselian valued field.
`isProperMap_compactFactor` then applies compact-source, Hausdorff-target
properness. Finally `isProperMap_coordinatePointMap_of_local` uses properness of
arbitrary products and the actual coordinate homeomorphisms. No cofinite
surjectivity condition is needed for properness.

These are reductions with explicit local inputs. This module does not prove the
local-field proper-point theorem or preservation of proper algebraic-space
morphisms under scheme base change, and does not yet prove the complete
`AdelicSpaceProperStagesStatement`.
