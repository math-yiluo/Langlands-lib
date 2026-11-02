# Integral-action schemes for projective abelian schemes over noetherian affine bases

This internal construction supplies the endomorphism representative and its
geometry required by the existing finite integral-action locus. Its inputs are
a commutative noetherian ring `R : Type u`, an actual abelian scheme `B` over
`S = Spec R`, a proof of the published `IsHProjective B.X.hom`, and a finite
integer basis `b : Basis I ℤ O` of a possibly noncommutative unital ring `O`.
The universes of `I` and `O` are independent. No endomorphism representative,
natural comparison, or geometric properties of such a representative are
additional inputs.

All declarations are in `Langlands.AbelianScheme.ProjectiveIntegralAction`.

The private existence lemma applies the published theorem
`AffineHomSchemePieces.affineHomSchemePieces` to `R`, `B` and its projectivity
proof. It retains the resulting actual scheme `E/S` and its separated,
locally finite type and formally unramified structure morphism.
`Cartier.nonempty_iso_yoneda_of_affine` extends that same scheme's affine-test
comparison to all schemes over `S`. This retains the geometry of the
representative; it does not extract it from the weaker existential conclusion
of `RelativeEndomorphismRepresentabilityStatement`.

`endomorphismScheme` chooses this witness. The four associated instances
export separatedness, local finite type, formal unramifiedness and local
noetherianness. The last follows from local finite type over the noetherian
affine base. `endomorphismSchemeIso` chooses the natural representation on
all tests, and `endomorphismSchemeLocallyNoetherianIso` restricts it to the
unchanged full locally noetherian test category.

`scheme` is the actual equalizer constructed by
`relativeIntegralActionLocusTest` from this representative and basis.
Its equations are the unit equation and the ordered basis multiplication
equations in the actual relative endomorphism ring of `B`. The tuple power is
locally noetherian by local finite type over `S`; it is not assumed to be
locally noetherian merely because its factors are.

`inclusion` maps this scheme to the finite power of `endomorphismScheme`.
It is a closed immersion by the existing equalizer theorem for a separated
equation target. The scheme is separated and locally of finite type over `S`,
and hence locally noetherian, by the published action-locus geometry.
`schemeIso` naturally identifies its lifted functor of points with
`relativeIntegralActionFunctor B b` on every locally noetherian scheme over
`S` and every morphism of that full category.

`universalAction` is an actual unital ring homomorphism
`O →+* End(B_scheme)`, with the existing categorical multiplication convention.
It classifies the identity of the same equation locus. The theorem
`universalAction_existsUnique` specializes the published universal-action
classification: every actual integral action on `B_T` has a unique actual
map `T → scheme` whose canonical relative restriction of `universalAction`
is that action. Restriction uses `relativeEndRestrict`, including the
canonical comparisons between iterated pullbacks.

The provenance is internal composition of the independently published
relative endomorphism construction and affine-extension theorem with
`RelativeIntegralActionLocusGeometry` and `RelativeIntegralActionUniversal`.
This module adds no new source assertion. It constructs actions on pullbacks
of a supplied projective abelian scheme; it does not construct an integral
model of a rational action, an ambient abelian moduli scheme, or a representing
scheme for the normalized Harris CM problem. Rosati and determinant loci,
smoothness, projectivity of the action locus, and admissibility of a final CM
representative remain separate obligations.
