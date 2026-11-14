# Actual coefficient scalar maps and the rational Pi relation

This module constructs actual coefficient multiplication maps on module
presheaves and sheaves, their unit isomorphisms, and their compatibility
with sheafification and rationalization. It then identifies the actual
rational Pi automorphism's d-th power with the scalar-pi automorphism.
These are derived prerequisites for scalar triviality of the constructed
Deligne general linear action.

The original motivation is V. G. Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4). The source
introduces the actual coefficient algebra `O[Pi]/(Pi^d-pi)`, graded lattice
and tangent sheaves, and rational frame. Its representability theorem
identifies the relevant action on Deligne's formal scheme with a projective
linear action. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The maps and comparison identities below are derived infrastructure;
this module does not attribute separate scalar-sheaf lemmas to the source.

## Hypotheses and scalar maps

All carriers have the common universe `u`. Initially `R` is any commutative
ring and `X` any topological space packaged as `TopCat`. For a presheaf `P`
of `R`-modules, `coefficientPresheafScale a P` has component at an open `U`
the actual linear map `x ↦ a • x`. Restrictions are linear, so these maps
form a natural transformation. `coefficientSheafScale a M` uses the same
natural transformation on an actual module sheaf `M`.

`coefficientPresheafScale_naturality` and
`coefficientSheafScale_naturality` show that every actual module map
commutes with this scalar map. Their proofs use the component maps'
linearity. The `_one` and `_mul` identities give identity at coefficient
one and the composition formula

```text
scale(a*b) = scale(a) ≫ scale(b).
```

Here categorical composition applies the left map first; commutativity of
`R` identifies the resulting `b • (a • x)` with `(a*b) • x`.
`coefficientSheafUnitIso a M`, for `a : Rˣ`, has forward map multiplication
by `a` and inverse multiplication by `a⁻¹`. The composition formulas and
unit identities prove both genuine inverse equations.

## Sheafification and rationalization

`sheafification_coefficientScale` proves that the actual sheafification
functor sends the pointwise scalar transformation to coefficient
multiplication on the sheafified module. The proof uses
`sheafify_hom_ext`: two maps from a sheafification to a sheaf agree if
they agree after the sheafification unit. Naturality of that unit and
linearity of each of its components give the required equality. No
linearity instance for the sheafification functor is assumed.

For rationalization, `O` is a commutative ring and `F` a field equipped
with an `O`-algebra structure. No domain, fraction-field, valuation,
flatness, or nonvanishing premise is needed for the comparison identities.
`rationalPresheafFunctor_coefficientScale` identifies extension of the
integral scalar `a : O` with pointwise multiplication by `algebraMap O F a`.
The proof uses scalar-extension hom extensionality: it is enough to test
`1 ⊗ m`, where the equation is exactly `O`-linearity of the extension and
restriction adjunction's unit. `rationalSheafFunctor_coefficientScale`
then combines this equality with the sheafification comparison.

## The actual rational Pi relation

Let `d : N`, `pi : O`, and let `M` be any actual sheaf of modules over
`PiAlgebra d pi`, the existing quotient algebra. There is no grading or
flatness assumption on `M` in these declarations.
`rationalPiPresheaf_relation_coefficientScale` restates the previously
proved rational presheaf relation using the constructed pointwise scalar
map: its d-th power equals multiplication by `algebraMap O F pi`.
The imported relation comes from the algebra identity `Pi^d=pi`, not an
extra operator axiom.

Assume further `NeZero d` and `hpi : algebraMap O F pi ≠ 0`. The existing
`rationalPiAut` is then a genuine automorphism of the total rationalized
sheaf. `rationalPiAut_hom_pow` proves its forward endomorphism's d-th
power is `coefficientSheafScale (algebraMap O F pi)`. The proof applies
sheafification's endomorphism monoid homomorphism to the presheaf power
identity, then uses the scalar-sheafification comparison.
`rationalPiAut_pow` upgrades this to the automorphism equality

```text
rationalPiAut F X d pi M hpi ^ d
  = coefficientSheafUnitIso (Units.mk0 (algebraMap O F pi) hpi)
      (rationalLattice F X d pi M).
```

Automorphism extensionality reduces this to the forward-map identity;
the actual map from automorphisms to endomorphisms preserves powers.
Both multiplication conventions compose functions in the usual order,
so the power comparison introduces no reversal issue.

## Remaining scope

This module does not yet construct homogeneous scalar isomorphisms of
the full Deligne four data, prove scalar triviality of the general linear
action, or descend it to the projective quotient. Base-change naturality,
the complete Nilp functor, the independent exterior-subsheaf comparison,
formal-module comparison and representability also remain further work.
No representing or universal object is supplied as an assumption.
