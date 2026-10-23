# Scalar extension of the unitary and similitude scheme models

Author: Worker 57.

## Scope and provenance

Let `R` and `S` be commutative rings with an `R`-algebra structure on `S`.
Let `A` be a possibly noncommutative `R`-algebra, `b` a finite `R`-basis of
`A`, and `σ` an `R`-linear algebra involution. All carriers and the basis index
have a common universe. This module constructs isomorphisms over `Spec S`
between the actual pullbacks of the original similitude and unitary group
schemes and the corresponding models formed from `S ⊗[R] A`, its extended
involution, and the scalar-extended basis `b.baseChange S`.

The isomorphisms preserve the multiplier and unitary inclusion. Their action
on every test scheme is the tensor-tower comparison on global sections. No
flatness, faithful scalar action, field, characteristic, or Noetherian
hypothesis is needed. No output scheme, comparison isomorphism, or naturality
assertion is supplied as an assumption.

The provenance is internal. `GroupSchemeBaseChange` supplies the actual
pullbacks and point comparisons; `InvolutionBaseChangeTower` supplies the
algebra and group equivalences; Mathlib supplies scalar extension of bases
and naturality of the global-sections/spectrum comparison. The existing
`GroupScheme.isoOfPoints` constructs an isomorphism of actual group schemes
from a natural multiplicative equivalence on every test scheme. No external
representability theorem is newly invoked. Smoothness, reductivity, signatures,
Harris PEL representability and scheme-level towers remain separate obligations.

## The actual scalar action on global sections

`scalarBaseMap R S` is `Spec.map (algebraMap R S)`. For any scheme `T` over
`Spec S`, `restrictedSections R S T` is the commutative `R`-algebra returned
by relative global sections of the composite `T → Spec S → Spec R`. Its
underlying ring is `Γ(T, O_T)` with this structural `R`-action.

The local instance `sectionsSAlgebra` equips the same ring with the structural
`S`-action from relative global sections over `Spec S`. The local instance
`sectionsScalarTower` proves that these two actions form a compatible scalar
tower. It does not replace the original `R`-action by fiat. The proof expresses
both algebra maps using `Scheme.ΓSpecIso.inv` and the structure morphism on
global sections, then applies `Scheme.Hom.comp_appTop` and
`Scheme.ΓSpecIso_inv_naturality`. The construction applies to every test scheme,
without an affine hypothesis on `T`.

## Similitude scheme comparison

`scalarExtensionPointsEquiv S b σ T` is a multiplicative equivalence from
points of the actual pullback to points of the model built over `S`. It
composes three existing multiplicative equivalences:

1. Pullback points to similitudes of `Γ(T,O_T) ⊗[R] A`, using the structural
   `R`-action above.
2. The tensor-tower equivalence to similitudes of
   `Γ(T,O_T) ⊗[S] (S ⊗[R] A)`.
3. The inverse of the point comparison for the actual model formed over `S`.

`scalarExtensionPointsEquiv_apply` identifies the induced algebraic point as
`baseChangeTowerSimilitudes` of the original one. Its algebra unit transforms
by `t ⊗ a ↦ t ⊗ (1 ⊗ a)` and its scalar multiplier is unchanged, by the
imported tower formulas.

`scalarExtensionPointsEquiv_naturality` proves compatibility with every map
`a : T' → T` over `Spec S`. It combines both original point naturality
lemmas with coefficient naturality of the tensor tower. The coefficient maps
on the two presentations are the maps on global sections induced by `a`;
the scalar-tower instance justifies restriction of the `S`-algebra map to `R`.

`scalarExtensionIso` applies `GroupScheme.isoOfPoints` to this natural family.
Thus its domain is the categorical pullback group scheme and its codomain
is the constructed finite-basis coordinate model over `S`, including their
group laws. `scalarExtensionIso_points` proves the tensor-tower formula for
postcomposition with this actual isomorphism.

`scalarExtensionIso_multiplier` is equality of morphisms of group schemes:
the comparison followed by the new model's multiplier equals the base-changed
old multiplier. Both land in the same `Gm` over `Spec S`; the latter already
includes the canonical base-change isomorphism for `Gm`. The proof uses
extensionality on every test scheme, the two multiplier point formulas,
and equality of the unchanged scalar coordinates.

## Unitary scheme comparison

`scalarExtensionUnitaryPointsEquiv` composes the analogous pullback unitary
point equivalence, `baseChangeTowerUnitary`, and the inverse of the new
unitary model's point equivalence. Both unitary schemes here are the actual
kernels of their respective multiplier morphisms.

`scalarExtensionUnitaryPointsEquiv_apply` gives the unitary tensor-tower
formula. Its naturality theorem proves equality by injectivity of the point
comparison, subgroup and unit extensionality, the existing unitary point
restriction formulas, and `baseChangeTowerEquiv_naturality` on the underlying
algebra. It does not assume a separate unitary coefficient functor.

`scalarExtensionUnitaryIso` is the resulting isomorphism of actual unitary
group schemes, and `scalarExtensionUnitaryIso_points` gives its action on
every test scheme. Finally, `scalarExtensionIso_unitaryInclusion` proves the
commuting square whose top and bottom maps are the two model isomorphisms
and whose vertical maps are the actual unitary inclusions. Its proof reduces
the square to points and then to `baseChangeTowerUnitary_inclusion`.
