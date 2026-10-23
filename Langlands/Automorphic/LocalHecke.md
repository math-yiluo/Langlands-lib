# Local Hecke operators on actual automorphic forms

For every number field `K : Type u`, natural rank `n` and finite place `v`,
this module integrates the smooth representation `automorphicLocalRightAction`
on the existing complex space of automorphic forms. It uses the actual topology
on `FiniteLocalGL K n v`, a supplied Borel measurable structure, and a supplied
left Haar measure `μ`. It does not choose a measure or impose a normalization on
its mass. Rank zero is included.

`automorphicLocalHeckeAction` is a nonunital complex algebra homomorphism from
the existing measure-indexed local convolution algebra to complex linear
endomorphisms of actual forms. The integration is the existing finite-fiber
algebraic integration of a smooth action. No topology or norm is imposed on
the form space. Applying the existing algebraic evaluation functional proves

\[
 (R_v(h)f)(x)=
 \int_{GL_n(K_v)} h(g)\,
 f\bigl(x\,\operatorname{ofFinite}(\operatorname{localInclusion}_v(g))\bigr)\,d\mu(g).
\]

The multiplication and scalar laws are inherited from `Hecke.heckeAction`.
The positive right-translation formula has no inverse. The convolution
convention remains the existing left-Haar convention.

For any compact open subgroup `L` of the actual local group,
`automorphicLocalHeckeCornerAction` is the genuine unital corner action on the
existing `L`-fixed-vector submodule. Its unit is the normalized subgroup
indicator, regardless of the supplied Haar measure's normalization.
`automorphicLocalHeckeAction_normalizedIndicator_eq_self_iff` identifies its
fixed vectors exactly. Each form is fixed by such an indicator: intersect a
smooth open stabilizer with the actual compact open `localIntegral` subgroup.
The intersection is compact because the open stabilizer is also closed.
This local unit proves nondegeneracy of the local Hecke action.

`automorphicLocalSphericalAction` specializes the corner to `localIntegral`.
It constructs the action on actual spherical vectors; it does not assert
commutativity of that corner, identify a Satake transform, or impose a dimension
on the fixed-vector space.

For every invariant ambient restriction `S`, the module constructs
`restrictedAutomorphicLocalHeckeAction` on `RestrictedAutomorphicForms K n S`.
Integration naturality proves that the existing injective local inclusion
intertwines these operators with those on all forms. Consequently the scalar
evaluation formula is identical and the same local units give nondegeneracy.
The corresponding unital corner action uses that restricted space's own local
fixed-vector submodule. These constructions apply directly to the existing
central-character and cuspidal specializations of `S`; no new carrier is used.

For distinct places `v` and `w`, translation at `w` is an intertwiner of the
action at `v`, by the already proved commutation of local actions.
Naturality of integration first proves that local Hecke operators at `v`
commute with translations at `w`. Bundling each such operator as a local
intertwiner at `w` and applying naturality again proves commutation with every
Hecke operator at `w`. The two Borel Haar measures are independent. No
comparison with a global product measure or Fubini argument is needed.

The provenance is internal: this module specializes `LocalAction`, the
evaluation functional from `FiniteHecke`, and the published integrated-action,
normalized-indicator and corner-action constructions. Its new consequences
follow from their proved naturality and the actual compact integral subgroup.
No additional external-literature theorem is asserted. The construction does
not prove admissibility, irreducibility, a restricted tensor factorization,
Satake parameter existence, or equality with a globally integrated test
function.
