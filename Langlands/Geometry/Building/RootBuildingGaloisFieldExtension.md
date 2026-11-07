# Galois fixation of actual field-extended building points

Let `k` and `K` be fields in an arbitrary common universe with a supplied
`k`-algebra structure on `K`. All field extensions, characters, group points,
apartments and quotients in this module are the actual imported constructions.
No finiteness, algebraicity or Galois-extension premise is used.

`GaloisPointComparison.rationalConjugate_rationalExtend` proves that the
existing rational-point extension is fixed by every coefficient automorphism.
The multiplicative comparison with coefficient points is injective. Under
this comparison the assertion is the existing `GaloisPoint.conjugate_extend`
identity.

For any commutative group scheme `S`, group scheme `G` over `k`, and arbitrary
upstairs root-function family, `RootFunctionFamily.fieldRestrict_galoisAction`
proves that literal family restriction is invariant under the actual
coefficient action. At an original character and an original rational point,
the action uses their inverse coefficient transforms. The pulled-back
character is fixed by `characterLattice.galoisRepresentation_baseChange`,
and the extended rational point is fixed by the preceding identity. Thus
both arguments of the arbitrary family are unchanged. This result requires
no splitness, smoothness, affine hypothesis or valuation law.

For the apartment and quotient conclusions, assume that `G` is affine and
smooth over `k`. Supply a monomorphic inclusion `i : S.toGrp ⟶ G`, splitness
of `S`, original `RelativeRoot.HasOppositeFactorPairs i`, a multiplicative
real-valued unit homomorphism `omega` on `K`, and a base-field unit on which
its restriction is nonzero. Write `S_K`, `G_K` and `i_K` for the literal base
changes. Their needed affine and monomorphism instances follow by pullback.
Supply `D : KPApartmentData i_K (fun t => (omega t).toAdd)` and
`hD : GaloisStable k K i D`. In particular the same full nonempty valuation
class and its coefficient stability are inputs.

`fieldRestrictPoint_galoisAction` applies the family identity to apartment
points. The existing actual restriction map on this supplied class is
injective. Consequently `galoisAction_eq_self_of_fieldRestrict` proves that
the actual coefficient action fixes every point of `D.Apartment`. The
split torus upstairs is precisely the base change of the original split
torus; this assertion does not concern a proper enlargement of that torus.

`galoisQuotientAction_fieldExtendBuilding` proves that the image of the
existing `fieldExtendBuilding` is fixed under the actual coefficient action
on the same `D.ReducedBuilding`. Express a source quotient point as an
original rational group element acting on a source apartment point. The
extension map sends it to the extended group element acting on the lifted
apartment point. Semilinearity of the quotient coefficient action, fixation
of extended group elements, its apartment-map formula, and pointwise
fixation of the apartment prove the identity. The original quotient and
original rational-point action are used throughout.

`fieldExtendFixedBuilding` packages that same map with codomain the subtype
of points fixed by every actual coefficient automorphism. Its value formula
is definitional. `fieldExtendFixedBuilding_injective` inherits injectivity
from `fieldExtendBuilding_injective`, under exactly its two geometric
premises: common translated source apartments and injectivity of the
upstairs apartment map. These geometric properties are not assumed for the
fixed-image containment itself.

This is an internal derivation from published field restriction, coefficient
transport and quotient constructions. It introduces no external literature
claim. It proves containment in a fixed locus, with conditional injectivity;
it does not prove equality with that locus or construct a canonical stable
class. Initial apartment existence, larger-torus restriction, the complete
NPC metric and orbit continuity, and the original supplied-model special
point, integral-points stabilizer identity and unique fixation remain
separate obligations. The unconditional `BuildingComparisonStatement`
remains open.
