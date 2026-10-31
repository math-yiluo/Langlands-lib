# Canonical scalar sections on affine Čech factors

## Scope and provenance

This internal construction works over actual schemes and module sheaves in
an arbitrary common universe `u`. Let `φ : R ⟶ S`, `f : X ⟶ Spec R`,
`f' : Y ⟶ Spec S`, and `g : Y ⟶ X` form a commutative square. For a
quasi-coherent module sheaf `M` on `X`, the file proves that the actual
`scalarCechSectionsMap` induced by the pullback-pushforward adjunction unit
is an isomorphism when the square is Cartesian, `g` is affine, and the
specified ordered affine cover has affine intersections. It also gives
the resulting quasi-isomorphism. Separatedness of `f` supplies the
affine-intersection hypothesis in the final two lemmas.

These are internal consequences of the specified Čech maps,
`AffineCartesianSectionsBaseChange`, restriction and pullback comparisons,
and Mathlib's Cartesian-open and affine-intersection results. No additional
external theorem is asserted or cited.

## The restricted pullback unit

For open immersions `i : Z ⟶ X`, `i' : Z' ⟶ Y` and a map `k : Z' ⟶ Z`
with `k ≫ i = i' ≫ g`, `restrictedUnitPushforward` is the composite
from `i_* (M|Z)` to `g_* i'_* (i'^* g^* M)` consisting of:

1. the comparison from restriction along `i` to pullback along `i`;
2. the pullback-pushforward unit for `k`, pushed forward along `i`;
3. the pullback comparison for the commutative square;
4. the pushforward comparison for that square.

The private lemma `restrict_unit_hom_ext` shows that maps out of
`i_* (M|Z)` into `i_* P` are determined by composition with the restriction
unit of `M`. Pushforward along an open immersion is fully faithful:
write the two maps as pushforwards, then use injectivity of the
restriction-adjunction hom-set equivalence.

`restrictedUnitPushforward_eq` applies this argument after cancelling the
pushforward-square isomorphism. A map compatible with the two restriction
units therefore becomes the specified restricted pullback unit after
replacing restriction by pullback on the target. The proof uses
`restrictAdjunction_unit_restrictFunctorIsoPullback` and
`unit_comp_pushforwardSquareIso_eq` for the two adjunction comparisons.

For opens `W` and `W'` with `W' ≤ g ⁻¹ᵁ W`,
`sheafOnPushforward_pullbackUnit_comp` specializes this result to the actual
`sheafOnPushforward` map. Its required compatibility is exactly the
previously implemented `unit_sheafOnPushforward`.

## Identifying the actual factor map

`factorPullbackSectionsIso` identifies relative sections of `sheafOn M W`
with relative sections of `W.ι^* M` over `W.ι ≫ f`. It applies relative
sections to the pushed-forward restriction-pullback isomorphism, then
uses the composition isomorphism for relative sections.

`factorSectionsMap_pullbackUnit_comp` identifies the actual ordinary
factor map with `sectionsBaseChangeMap` on the restricted square,
conjugated by these two sections isomorphisms and followed by relative
sections of the pullback-square isomorphism. The proof evaluates the
preceding sheaf-level equality at the top open and an arbitrary section.
The definitions of the pushforward comparisons give the desired equality.

`scalarFactorSectionsMap_pullbackUnit_comp` gives the same equality for
the actual scalar adjunct, with scalar extension applied to the source
sections isomorphism. Injectivity and naturality of the
extension/restriction-of-scalars adjunction reduce it to the ordinary
factor identity.

`isIso_scalarFactorSectionsMap_pullbackUnit_of_isPullback` assumes that
both restricted schemes are affine and that their square over `φ` is
Cartesian. Restriction of a quasi-coherent sheaf is quasi-coherent, and
the restriction-pullback isomorphism transfers this to `W.ι^* M`.
The canonical affine Cartesian scalar sections theorem then makes the
middle map in the preceding identity invertible. The remaining factors
are images of isomorphisms, so cancellation of the target sections
isomorphism proves invertibility of the actual scalar factor map.
This factor result needs no affineness assumption on the original `g`.

## The inverse-image cover and assembly

`isPullback_resLE_baseChange` proves that restricting the original
Cartesian square to `W' = g ⁻¹ᵁ W` preserves its Cartesian property.
After substituting this equality, Mathlib identifies `g.resLE` with
`g ∣_ W`. The standard Cartesian restriction square pastes vertically
with the original square.

`isIso_scalarFactorSectionsMap_inverseImageCover` applies this to each
intersection in the inverse-image ordered cover. That intersection is
the full preimage of the corresponding source intersection. The latter
is affine by the explicit hypothesis; its preimage is affine because
`g` is affine. The restricted-square factor theorem applies to precisely
the factor map in `scalarCechSectionsMap`.

`isIso_scalarCechSectionsMap_of_isPullback` assembles all these factor
results using `isIso_scalarCechSectionsMap_of_factors`. That theorem
identifies each degree map with the finite biproduct of its actual factor
maps. Thus this conclusion is invertibility of the specified cochain
map, with source the scalar extension of the relative sections of
`cechComplex 𝒰 M`, and target the relative sections of the inverse-image
Čech complex for `g^* M`.

`quasiIso_scalarCechSectionsMap_of_isPullback` uses the standard instance
that an isomorphism of complexes is a quasi-isomorphism.

`isAffineOpen_inter_of_isSeparated` proves the affine-intersection
hypothesis for a separated source scheme. Each ordered-cover
intersection is a nonempty finite intersection of affine opens;
Mathlib's `IsAffineOpen.iInf` applies since a separated scheme has
affine diagonal. In
`isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated`, separatedness
of `f` and of the affine base implies absolute separatedness of `X` by
composition with the terminal morphism of `Spec R`. The intersection
lemma then supplies every factor hypothesis. The final
`quasiIso_scalarCechSectionsMap_of_isPullback_of_isSeparated` again
uses the isomorphism-to-quasi-isomorphism instance.

No flatness, noetherian, reducedness or properness assumption is needed
for these results about the Čech scalar sections map. They do not prove
acyclicity of the Čech terms, identify the augmentation as an acyclic
resolution for relative sections, prove localization base change for
derived sections, or prove the relative rigidified cube statement.
Those comparisons require further results.
