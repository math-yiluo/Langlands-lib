# Pullback of actual admissible Deligne classes

This module proves preservation of the existing three-condition
`SheafPreDatum.Admissible` predicate and constructs pullback on the existing
admissible four-data objects and their isomorphism classes. Identity and
composition become equalities on these classes.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the four data
`eta,T,u,r` at the page boundary and conditions (a), (b), (c) in the
opening paragraph of p.110. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The preservation and quotient constructions here are derived infrastructure;
they are not separate theorems quoted from Drinfeld.

## Parameters and existing constructions

The parameters are a commutative ring `O`, a positive integer `d`, an
element `π : O`, an `O`-algebra field `F`, schemes in the same universe,
and an actual map `φ : O →+* Γ(S, ⊤)`. We require
`hπ : algebraMap O F π ≠ 0`. For any scheme map `f : S' ⟶ S`,
the scalar map of the result is the constructed
`pulledGlobalScalar f φ = f.appTop.hom.comp φ`. No flatness or nilpotence
hypothesis on this base map is needed.

The imported `SheafPreDatum` contains the actual lattice, rational frame,
structural tangent sheaf and Pi-compatible map `u` with local generation.
The imported `Admissible` predicate is the conjunction of constancy on the
Pi-zero loci, injectivity of the actual total quotient-to-residue-fibre
map, and the existing all-integer stalkwise determinant normalization.
`SheafDatum` is its subtype, and `SheafDatum.IsoClass` is the quotient
whose relation is existence of an actual four-data isomorphism.

## Preservation of the three conditions

`SheafPreDatum.admissible_pullback` combines three proved preservation
results for the same actual `SheafPreDatum.pullback f`:

- `ConstantOnPiZeroLoci.pullback` uses the actual inverse-image Pi-zero
  locus comparison and the inverse image of a constant module sheaf.
- `residueFibreInjective_pullback` uses the actual eta quotient
  isomorphism and the tangent residue-fibre comparison; extension along
  the residue-field map is injective on the original fibre.
- `DeterminantNormalized.pullback` maps the original determinant equality
  through the exterior power of the actual rational stalk comparison.
  The component and normalized frame lattices are transported by that
  map for every integer, and the Pi-zero locus comparison supplies the
  required original point.

The combination theorem simply assembles these three conclusions.
`SheafDatum.pullback` pairs the actual pulled preliminary datum with
that proved conjunction. `pullback_val` records its underlying datum.

## Pullback on genuine isomorphism classes

`SheafDatum.IsoClass.pullback` uses `Quotient.map` on the preceding
object construction. For two representatives related by a genuine
four-data isomorphism, the existing `SheafPreDatum.pullbackIso` supplies
a genuine isomorphism of their pulled representatives. Both objects
already have their proved admissibility conditions, so this is exactly
the relation used by the admissible quotient.

`pullback_mk` identifies the map on a representative.
`toPreliminary_pullback` proves that forgetting admissibility commutes
with pullback; quotient induction reduces it to the defining formula.
`pullback_id` and `pullback_comp` are literal equalities on admissible
classes. Quotient induction and `Quotient.sound` reduce them to the
constructed four-data isomorphisms `pullbackIdIso` and
`pullbackCompIso`. The latter compares successive pullbacks with
pullback along `g ≫ f`. The scalar maps on the identity and composite
bases agree definitionally, so no additional scalar identification is
assumed.

## Scope

This is preservation of the existing constructed predicate. Its
determinant condition retains the documented boundary: integral
injectivity, tensor/stalk comparison, and equivalence with an
independently constructed equality of exterior-power subsheaves are
not supplied here. No existence theorem for admissible data is claimed.
Specialization of this class map to a functor on actual `Nilp` algebras,
the normalized `PGL(d,F)` action, comparison with special formal modules,
and representability remain further constructions. No representing
object, universal object or uniformization isomorphism is an input.
