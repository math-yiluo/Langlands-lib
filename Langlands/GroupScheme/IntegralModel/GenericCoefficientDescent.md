# Automatic descent from the prescribed generic map

This internal construction concerns the actual supplied integral models `M` and
`N` over a domain `R` with fraction field `K`, in every common universe `u`.
Let `A` be a domain with fraction field `L`, with the specified algebras and
scalar towers giving the commuting coefficient square `R → A`, `K → L`.
The generic identifications are exactly those of `M`, `N` and their existing
`baseChange A L` constructions.

## Automatic compatibility

`Hom.canonicalCompatible` takes an upstairs model morphism extending the scalar
extension of a prescribed original generic map `f : G ⟶ H`. If
`Spec A → Spec R` is flat, its actual underlying group-scheme map respects the
canonical Čech data of the two original models. Surjectivity is not needed
for this compatibility assertion. The statement has no smoothness,
reductivity, local-field, splitness or finite-degree premise.

The proof first establishes an abstract scheme comparison
`GenericCoefficientDescent.relation_eq_of_generic_factor`. For `a : X → Z`
and a quasi-compact schematically dominant `i : W → X`, flatness of `a` and
`i ≫ a` makes the natural map `W ×_Z W → X ×_Z X` schematically dominant.
Both changes of factor are actual pullback maps, expressed using pullback
pasting isomorphisms. If `i ≫ h` factors through `c : W → T` and
`c ≫ k = i ≫ a` for a monomorphism `k : T → Z`, the two projections from
`W ×_Z W` followed by `c` agree by cancellation of `k`. Thus their
`h`-values agree. The published separated-target dominance lemma reflects
this equality to `X ×_Z X`.

For the models, `X` is the actual coefficient pullback of `M`, `Z` is the
original model scheme and `W` is the generic fibre of `X`. The generic
inclusion is quasi-compact and schematically dominant: the inclusion of a
domain in its fraction field has dense spectrum map, the base is reduced,
and the flat model preserves scheme-theoretic dominance under pullback.
The required flatness follows from the flat coefficient map and fraction-field
localization. The monomorphism `k` is the original model's generic-fibre
inclusion. The supplied upstairs generic compatibility equation and
`baseChangeGenericIso_hom_fst` give both factorizations using the original
generic identifications. Finally, the canonical Čech overlap maps factor
through `X ×_Z X`. The overlap isomorphisms preserve projection to the
original model, and pullback extensionality gives the required actual
morphism equality on the overlap.

## Descent and exact recovery

For the rest of the construction, `Spec A → Spec R` is also surjective, hence
is an fpqc cover (quasi-compactness is available for these affine spectra).
`Hom.descendFromCoefficients` applies the existing
`Hom.descendCoefficients` with the automatically proved compatibility.
Its output is an actual `M.Hom N f` for the original prescribed `f`.
`Hom.baseChange_descendFromCoefficients` recovers exactly the supplied upstairs
map after coefficient base change, and
`Hom.descendFromCoefficients_unique` proves uniqueness among original
extensions having that recovery equation.

`Hom.coefficientEquiv` is an equivalence between the original morphism type
`M.Hom N f` and the upstairs model morphisms extending the coefficient
extension of `f`. Its forward map is the existing
`Hom.baseChangeCoefficients`; its inverse is the constructed descent. The
inverse laws use uniqueness of descent and exact recovery, with the
propositional generic-compatibility field identified by structure equality.

`Iso.descendFromCoefficients` similarly descends an actual upstairs model
isomorphism extending the coefficient extension of a prescribed original
generic isomorphism. It uses automatic compatibility of the forward map
and the existing `Iso.descendCoefficients` construction.
`Iso.baseChange_descendFromCoefficients` recovers the full supplied
upstairs group-scheme isomorphism. For a generic-identity isomorphism,
`integralPoints_eq_of_coefficientIso` applies the existing original-image
transport to the descended isomorphism. Its conclusion is literal equality
of `M.integralPoints` and `N.integralPoints` using their original generic
identifications.

## Provenance and scope

This is an internal derivation from actual pullbacks, flat preservation of
scheme-theoretic dominance, localization, the published separated-target
generic rigidity lemma, canonical Čech data, and coefficient morphism
and isomorphism descent. The implemented argument is the double-relation
proof above. It imports no additional external structural theorem.

It constructs descent of a supplied upstairs extension, with no additional
Čech compatibility premise. It does not construct that upstairs extension,
a canonical good-model comparison, a building, or a special point, and does
not prove `BuildingComparisonStatement`.
