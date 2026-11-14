# Coherent pullback of Deligne's four preliminary sheaf data

This module constructs canonical identity and composition isomorphisms for
the actual preliminary data `eta,T,u,r`. It proves their naturality,
associativity and both unit equations, and the resulting identity and
composition laws on preliminary isomorphism classes.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed p.109 (PDF p.3), the final paragraph defining
`eta,T,u,r`, continuing on printed p.110 (PDF p.4). Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The categorical comparisons and their proofs are derived infrastructure,
rather than an assertion that Drinfeld states these equations separately.

The parameters are a commutative ring `O`, a positive integer `d`, an
element `π : O`, a field `F` with an `O`-algebra structure, schemes in one
universe, and an actual homomorphism `φ : O →+* Γ(S, ⊤)`. Neither a local
field assumption nor nilpotence is required for these comparison laws.
For `f : S' ⟶ S`, the new scalar map is the actual
`pulledGlobalScalar f φ = f.appTop.hom.comp φ`. Identity and successive
scalar maps agree definitionally with the corresponding identity and
composite-base scalar maps.

The imported `SheafPreDatum` includes a graded flat coefficient lattice
with its full rational degree-zero frame, a graded structural tangent
sheaf with line components and Pi operator, and the total and homogeneous
maps `u` satisfying local structural generation. The existing `pullback`
already constructs these data and derives local generation on the new base.
This module supplies coherence for that same construction.

## Constructing a genuine four-data isomorphism

`SheafPreDatum.isoOfComponents` takes an isomorphism of the actual framed
lattices, an isomorphism of the actual graded tangent sheaves, and the
forward square for total `u`. It constructs the morphism and its inverse.
To derive the inverse square, the proof applies the actual forgetful
functors to both isomorphisms and cancels their inverses. No inverse
square is assumed. The two inverse equations follow from
`SheafPreDatum.Hom.ext`.

The imported morphism definition requires preservation of the full frame,
the grading and Pi, and the total `u` square. Its
`Hom.uComponent_naturality` theorem also gives preservation of the
specified homogeneous `u` restrictions. Thus the isomorphisms assembled
here preserve all four data, including the specified homogeneous maps.

## Compatibility of the actual total map

Write `P_f` for ordinary inverse image of `O`-module sheaves, `L` for
restriction of coefficient scalars, `U` for forgetting structural scalars,
and `Q_f` for the canonical map `structuralPullbackComparison f φ`.
The existing pulled total map has the formula

```text
u_f = e_f.inv ≫ P_f.map u ≫ Q_f.app T,
```

where `e_f` is `inverseImageLatticeScalarIso` on the actual total lattice.
The canonical map `Q_f` is not assumed invertible.

`pullbackU_id` proves that the framed-lattice identity comparison and
graded structural identity comparison commute with this `u_f`. Restriction
of scalars coherence identifies the lattice comparison with
`e_id.inv` followed by ordinary identity comparison. Naturality of the
ordinary identity comparison at `u`, followed by
`structuralPullbackComparison_id`, proves the square.

For `f : S' ⟶ S` and `g : S'' ⟶ S'`, `pullbackU_comp` proves the corresponding
square from iterated pullback to pullback along `g ≫ f`. Let `c_O` and
`c_R` be the ordinary composition comparisons for `O` and the actual
coefficient algebra `PiAlgebra d π`. Restriction coherence on the total
lattice gives

```text
c_O.hom ≫ e_(gf).hom =
  P_g.map e_f.hom ≫ e_g.hom ≫ L.map c_R.hom.
```

Cancellation with the actual isomorphisms gives

```text
L.map c_R.hom ≫ e_(gf).inv =
  e_g.inv ≫ P_g.map e_f.inv ≫ c_O.hom.
```

The proof substitutes this into the composite-base pulled `u`, applies
naturality of `c_O` at the original `u`, and then uses
`structuralPullbackComparison_comp` at the actual tangent module.
Functoriality and associativity identify the result with the iterated
pulled `u` followed by the underlying structural composition comparison.
All coefficient comparisons concern the actual lattice and tangent
objects; compatibility of `u` is proved here.

## Natural comparisons and coherence

`pullbackIdIso` uses the framed-lattice `inverseImageIdIso`, the tangent
`pullbackIdIso` and `pullbackU_id` in `isoOfComponents`. Its direction is
`D.pullback (𝟙 S) ≅ D`.

`pullbackCompIso f g` similarly uses the framed-lattice
`inverseImageCompIso f.base g.base`, the tangent `pullbackCompIso f g` and
`pullbackU_comp f g`. Its direction is
`(D.pullback f).pullback g ≅ D.pullback (g ≫ f)`.

`pullbackIdNatIso` and `pullbackCompNatIso` prove naturality for every
actual four-data morphism by reducing to the two component naturality
equations with `Hom.ext`. The following equations hold as equalities
of genuine four-data isomorphisms:

- `pullbackCompIso_assoc`: for three successive base maps, pulling the
  first composition comparison through the third map and then composing
  equals first comparing the last two pullbacks and then comparing with
  pullback along the full composite.
- `pullbackCompIso_id_left`: comparison with identity on the original
  base is the pulled identity comparison.
- `pullbackCompIso_id_right`: comparison with identity on the new base
  is the identity comparison of the already pulled object.

Their proofs use `Iso.ext` and `Hom.ext` to reduce to the existing framed
lattice and graded tangent associativity and unit equations.

Finally, `SheafPreDatum.IsoClass.pullback_id` and `pullback_comp` are
literal equalities on the quotient by genuine four-data isomorphism.
Quotient induction reduces each equality to one object, and
`Quotient.sound` applies the constructed comparison isomorphism.

## Scope

These are coherent pullbacks of preliminary data and laws on preliminary
classes. Preservation of the three admissibility conditions, the admissible
`Nilp` functor, integral determinant comparison, the normalized `PGL(d,F)`
action and the comparison with special formal modules remain separate
obligations. In particular, this module does not assert Drinfeld's
Proposition 2.4, Section 2 B, printed p.110 (PDF p.4), or representability,
and takes no representing object, universal object or uniformization
isomorphism as input.
