# Finite residue-field modules on actual Artinian Picard obstruction spaces

Let `f : X → Spec k` be proper, with `k` a commutative ring, and let
`q : A → B` be an arrow of the published augmented local Artinian test
category with residue field `K`. The field is arbitrary, and all rings,
schemes and module carriers retain common arbitrary universe `u`. The tests
include a surjective augmentation `A → K`; no section or coefficient field
is chosen.

`idealModule f q` is the actual structure-map kernel module for
`X_B → X_A`. `Cohomology f q n` abbreviates exactly the existing
`SquareZeroUnitCohomology.idealCohomology` of this map: the right-derived
global sections of this actual ideal module. Its additive group and
original global-section-ring action are retained. In degree two this is
the target of the actual pointed lifting obstruction from
`ArtinianSquareZeroPicardLifting`.

For every surjective `q`, `relativeCohomology_finite` proves that relative
ideal cohomology is finite over `A` in every degree. Hopkins–Levitzki makes
the Artinian ring noetherian. The actual relative projection is proper by
base change, hence locally of finite type, so `X_A` is locally noetherian.
The actual relative closed immersion has a quasi-coherent ideal module
with finite affine sections. The published proper coherent cohomology
finiteness theorem therefore applies. The explicit base-spectrum
local-noetherian instance identifies the same test scheme used by the
relative projection.

Suppose now that `q` is elementary: it is surjective and
`maximalIdeal A * ker q = 0`. `affineSections_smul_eq_zero` shows that the
maximal ideal annihilates every actual affine ideal section. The affine
kernel formula from `ArtinianSquareZeroPicardLifting` identifies the
section ideal with the image of `ker q`; preservation of ideal products
and zero by ideal image proves annihilation. The affine intersections of
a finite ordered affine cover of `X_A` are affine because the relative
projection is separated. Thus every term of the actual alternating Čech
complex is annihilated. The helper `shortComplex_smul_eq_zero` uses the
injective cycles inclusion and the surjective homology projection to pass
annihilation from cochains to homology. The published linear Čech
comparison proves `relativeCohomology_smul_eq_zero` in every degree.

`sourceModule` restricts the unchanged ideal-cohomology group's
existing global-ring action along the actual relative structure ring
homomorphism. `relativeEquiv` is the published canonical comparison of
restricted global cohomology with relative cohomology, evaluated on the
actual ideal module. It transfers finiteness and annihilation to
`Cohomology f q n`, giving `cohomology_finite` and
`cohomology_smul_eq_zero` for this precise source-ring action.

The kernel of `A → K` equals the maximal ideal, so it annihilates this
module for elementary `q`. `residueAction` descends the actual source-ring
action homomorphism into additive endomorphisms by
`RingHom.liftOfSurjective`. `residueAction_unique` proves uniqueness among
actions whose composite with the augmentation is that source-ring action.
`residueModule` equips the same actual additive group with this `K`-action;
`augmentation_smul` proves that restriction along the augmentation recovers
the exact source-ring action. The underlying map of `identitySemilinear`
is the identity of this group, semilinear for `A → K`.

Finally `finiteDimensional` applies `Module.Finite.of_surjective` to this
semilinear identity and the already proved finite `A`-module. Consequently
all of these actual ideal-cohomology groups, including the obstruction
H², are finite dimensional over the specified residue field. Zero kernels
and arbitrary elementary-kernel dimensions are allowed. No flatness of
`f`, identification with a residue-fibre tensor product, or numerical
dimension formula is asserted.

This is an internal derivation from the actual Artinian test geometry,
affine kernel calculation, proper coherent cohomology finiteness, Čech
comparison, and scalar descent in Mathlib. It does not assert a complete
local hull, formal versality, algebraization, or the exact Picard stack
atlas theorem, all of which remain separate proof obligations.
