# Smooth actual relative automorphisms over a field

This internal construction uses the published global-functions, finite-algebra
units, and smooth base-change results. Fix an arbitrary field `k : Type u`, an
actual scheme `X : Scheme.{u}`, and a proper morphism `f : X → Spec k`.
Properness is the only additional hypothesis.

`fieldUnitScheme f` is the determinant-open scheme of units of the actual
algebra `Γ(X, O_X)` with the scalar action `GlobalFunctionsAlgebra.algebra f`
induced by the structure morphism. The published theorem
`FieldGlobalFunctions.finite_algebra f` makes this a finite module over `k`.
`Module.finBasis` supplies a basis indexed by the finite dimension, and
`FiniteAlgebraUnits.candidate` constructs the scheme from that basis.

`fieldUnitSchemeIso f` represents the full lifted relative-global-unit
presheaf by this actual scheme. The first isomorphism is `asIso` of the
specified `FiniteAlgebraUnits.candidateMap`, whose invertibility is the first
conjunct of the published `FiniteAlgebraUnits.representability`. Its target is
the finite-algebra unit presheaf. Composing with the inverse of
`FieldGlobalUnits.finiteAlgebraPresheafIso f` gives the relative global units of
`X`. This inverse comparison is the actual pullback of units along the base
change of `X.toSpecΓ`, as specified by the published canonical comparison.
Thus the representation is natural on the entire category of schemes over
`Spec k`.

`fieldUnitScheme_smooth f` is the second conjunct of the same finite-algebra
representability theorem, applied to the same finite basis. It proves ordinary
smoothness of the actual structure morphism of `fieldUnitScheme f`.

`field_hasSmoothUnitSchemes f` applies the published smooth-unit base-change
adapter to this scheme, its full natural representation, and its smoothness.
It gives smooth scheme representatives of restricted relative units on every
scheme slice. `field_hasSmoothRelativeAutomorphismSchemes f` then applies the
published scalar-automorphism comparison. Its target is the automorphism
presheaf formed directly from the actual relative Picard pseudofunctor, with
all coherent restriction maps, for every relative test scheme and every actual
line bundle on its fibre product with `X`.

All constructions retain universe `u`, arbitrary fields, nonreduced and
non-quasi-compact test schemes, and every actual line bundle. No equality
`Γ(X,O_X) = k`, chosen point, section, universal bundle, positive algebra rank,
reducedness, smoothness or projectivity of `X`, or flatness over its
global-functions spectrum is used. This contribution supplies the smooth
relative automorphism condition. It makes no claim of a stack atlas, a quotient,
or Picard-sheaf representability.
