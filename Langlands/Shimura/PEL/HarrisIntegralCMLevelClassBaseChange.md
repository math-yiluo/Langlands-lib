# Base naturality of actual integral Harris normalized classes

This internal unit proves base naturality for the existing map from actual
full-order integral Harris Weil levels to the unchanged normalized CM class
tower. It uses the actual universe-zero Harris CM arithmetic data, an abelian
scheme `B` over `S`, its supplied dual witness and polarization, and a morphism
`f : T' ⟶ T` of quasi-separated test schemes over `S`. The joint full-order CM
condition holds on the supplied action over `T`. Its target action is literally
`(relativeEndRestrict B f).comp a`; the existing restriction theorem derives
the joint condition for that action.

The source family has the prescribed relative dimension. The named
`Prerequisites`, duality naturality, Lie base-change naturality on `T`, finite
Weil transitions, adelic comparison, torsion statement, and ordered-pair dual-map
additivity on both test schemes remain inputs. All positive orders are
invertible and roots of unity are finite etale on both schemes. The field-valued
point `t` over `T'` and its composite with `f.left` have finite fibres on
finite-etale covers. No connectedness, local Noetherianity or algebraic closure
is required for these two class-square lemmas.

`harrisIntegralCMFullActionLevelOriginalClassRestriction` defines the natural
transformation which restricts a raw integral Harris orbit along `f`, lifts the
result to the normalized-class universe, and takes its original normalized CM
class over `T'`. Its domain is the original raw tower over `T` at `t ≫ f.left`;
its codomain is the original normalized CM class tower over `T'` at `t`.
This specializes the existing raw restriction and class maps to the actual
integral-family consumer.

`harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange` proves equality
of natural transformations on the entire original Harris level category.
One route restricts the actual raw fixed orbit to the direct family over `T'`
and then takes its original normalized CM class. The other first takes the
normalized class over `T` and then applies the existing
`classTowerBaseChangeAlong`. The latter includes equality transport between
`f.left ≫ (T.hom ≫ p)` and `T'.hom ≫ p`, obtained from the triangle of the
morphism in `Over S`. The field-valued source point is exactly `t ≫ f.left`.
The canonical pulled dual data are those already constructed by
`harrisIntegralCMLevelPullbackDualData` from each source action's own dual.

The proof expands aligned pullback into ordinary class pullback and the
source/target presentation transports. The source transport is the identity.
It takes components at a level and a lifted raw orbit, then reduces Type-category
composition and function application before projecting through the two
normalized class subtypes. The published presentation and class-pullback
projection lemmas identify the resulting ambient quotient classes. Finally
`Quotient.sound` applies
`harrisIntegralCMFullActionLevelRestriction_related`, the actual original
polarized rational-isogeny relation with the canonical comparison and multiplier
one. Thus the proof uses the existing relation and class image, with no change
to the moduli problem.

`harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange_dualData` proves
the same square for any constrained pulled dual-evaluation data on the actual
ordinary pullbacks. It rewrites the existing aligned class transformation by
`classTowerBaseChangeAlong_dualData` and applies the canonical square. This is
independence of auxiliary dual data, rather than an assumption of the square.

The provenance is internal: both lemmas derive naturality of the existing
integral-family class map from published family/duality constructions, the
actual rational-isogeny comparison, and the existing independence theorem.
This unit does not construct a representing scheme or prove admissibility,
smoothness or division projectivity. Compatibility of the corresponding maps
to all-geometric-point families and test-variable identity/composition remain
separate obligations of the surrounding representability proof.
