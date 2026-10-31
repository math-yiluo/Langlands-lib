# Universal perfect representatives under a scalar tower: proof

Author: Worker 137.

The theorem `universalPerfectSectionsScalarTower.{u}` proves the named
`UniversalPerfectSectionsScalarTowerStatement.{u}`. It retains the given
complex and chooses its ordinary scalar extension as the representative
over the new ring.

The helper `relativeDerivedSectionsIsoOfComp` specializes the published
scheme-isomorphism invariance of actual derived sections. It accepts
explicit equations identifying the source structure map and the map
used to pull back the coefficient. After substituting those equations,
module pullback composition identifies the coefficient with the
pullback by the scheme isomorphism, and
`relativeDerivedSectionsPullbackIso` finishes the comparison.

The helper `relativeDerivedSectionsScalarTowerIso` applies that result
to Mathlib's `pullbackLeftPullbackSndIso`, after rewriting contravariant
composition of `Spec` to express the direct pullback along `φ ≫ ψ`.
The standard projection equations establish both
equations needed by the first helper. A module pullback composition
isomorphism identifies the iterated coefficient pullback with pullback
along the composite projection. This constructs an actual
derived-category isomorphism from sections on the iterated pullback to
sections on the direct pullback.

For the main theorem, `isStrictlyPerfect_baseChange` supplies strict
perfection over `S`. The given comparison for `φ` supplies the
original-base comparison over `S`. For every further map `ψ`, the given
comparison for `φ ≫ ψ` is preceded by the inverse of
`baseChangeCompIso`, mapped into the derived category, and followed by
the inverse of the geometric helper above. Thus its source is the two
successive ordinary scalar extensions of the same given complex and
its target is actual derived sections of the iterated module pullback.

This is an internal composition of the published algebraic and
scheme-isomorphism transport APIs, generalized to arbitrary actual
modules in common universe `u`. It assumes the initial universal
representative, proves no existence theorem for smooth proper
families, and asserts no naturality of the given comparisons.
