# Actual integral scalar isomorphisms of Deligne's four data

This module constructs genuine homogeneous scalar automorphisms of the
lattice and tangent sheaves, and a frame- and u-preserving isomorphism
undoing reframing by the image of any integral coefficient unit.

These are derived algebraic constructions for the four data in V. G.
Drinfel'd, *Coverings of p-adic symmetric regions* (1976), Section 2 A,
printed pp.109–110 (PDF pp.3–4). The source defines the graded lattice,
graded tangent sheaf, homogeneous map u, and rational frame on a scheme
where pi is nilpotent, and states the projective action in the
representability theorem. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The scalar constructions below are derived infrastructure, not separately
attributed source theorems.

## Coefficients and the scalar frame change

All carriers have the common universe `u`. The coefficient ring `O` is
commutative, `F` is a field with an `O`-algebra structure, and `pi : O`.
The scalar linear group homomorphism `scalarReframeHom d F` sends a unit
`a : Fˣ` to the actual linear equivalence `v ↦ a • v` on `Fin d → F`.
Linearity and the scalar multiplication identities prove its group laws.
`constantSheaf_scalarReframeHom` identifies the image of this linear map
under the actual constant-sheaf functor with `coefficientSheafScale`.
The proof uses the published scalar comparison for sheafification.

For all the homogeneous constructions assume `NeZero d`. No injectivity
of `O → F`, discrete valuation, nonvanishing of pi, nilpotence, or
admissibility assumption is needed for these unit isomorphisms.

## Actual homogeneous lattice and tangent automorphisms

For an actual graded lattice `M`, `LatticePiSheaf.coefficientScale a M`
multiplies the total `PiAlgebra d pi` module sheaf by the image of `a : O`,
and each homogeneous component by `a`. The inclusion squares follow from
`latticeScalarFunctor_coefficientScale` and scalar naturality. The former
identity is checked on actual sections of the scalar-restricted sheaf.
Thus these are morphisms in the existing category of homogeneous lattices.
`LatticePiSheaf.coefficientUnitIso a M`, for `a : Oˣ`, uses these maps for
`a` and `a⁻¹`. Extensionality on the total maps, the scalar composition
formula, and the two unit equations prove both inverse identities.

Let `S` be a scheme. For any global section `b` of its structure sheaf,
`GradedPiSheaf.structuralScale b M` multiplies sections by the restriction
of `b`. It commutes with the actual Pi operator by linearity. Each actual
homogeneous subsheaf is a submodule and is therefore preserved by this
multiplication. `GradedPiSheaf.structuralUnitIso b M` uses a global unit
and its inverse; the restrictions preserve their products, so the two
compositions are identities. This construction applies to any structural
Pi parameter and does not require it to be invertible or nilpotent.

For a ring map `phi : O → Γ(S, top)`,
`structuralOSheafFunctor_structuralScalarEnd` proves that forgetting
structural scalars sends multiplication by `phi(a)` to the actual
O-coefficient map `coefficientSheafScale a`. Its proof is sectionwise.

## Undoing an integral-unit reframe

For a framed lattice `M` and `a : Oˣ`,
`FramedLatticePiSheaf.reframeIntegralUnitIso M a` is an actual isomorphism

```text
M.reframe F (scalarReframeHom d F (Units.map (algebraMap O F) a)) ≅ M.
```

Its lattice map is multiplication by `a⁻¹` on the total sheaf and every
homogeneous component. The frame square is proved using the imported
`isoOfTotalFrame`: after rationalization this lattice map becomes
multiplication by the field image of `a⁻¹`. Scalar naturality moves it
across the total frame; the constant-sheaf comparison identifies the
scalar reframe with multiplication by the field image of `a`. Their
product is one, giving the original total frame. The existing split
inclusion then recovers the actual degree-zero frame square through
`isoOfTotalFrame`.

The selected definition `SheafPreDatum.reframeIntegralUnitIso D a`
constructs the corresponding isomorphism of all four data:

```text
D.reframe (scalarReframeHom d F (Units.map (algebraMap O F) a)) ≅ D.
```

Its lattice part is the preceding framed isomorphism. Its tangent part
is structural multiplication by `phi(a⁻¹)`, with inverse multiplication
by `phi(a)`. For each direction the u square becomes scalar naturality
for the actual map `D.u`, using the lattice and structural forgetting
comparisons. Extensionality on the lattice and tangent morphisms and
their inverse equations give the two inverse equations in the category
of the full four data. No quotient relation or isomorphism witness is
assumed: the morphisms and their equations are constructed explicitly.

## Remaining scope

This module handles integral-unit scalar reframing of preliminary four
data. It does not yet prove triviality of the normalized action on
admissible classes for arbitrary field scalars, nor construct the PGL
quotient action. The uniformizer shift isomorphism, general scalar
triviality, base-change comparisons, the complete Nilp functor,
formal-module comparison, and representability remain further work.
