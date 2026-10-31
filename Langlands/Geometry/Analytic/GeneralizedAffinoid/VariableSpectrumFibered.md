# Actual quotient spectra and the operator-group fibrations

This internally derived module compares the already constructed fibration
of actual finite positive-polyradius quotient actions with the fibration of
actual jointly continuous actions on topological spaces. The motivating
operator-group convention and fibration assertion are Berkovich, *Étale
equivariant sheaves on p-adic analytic spaces* (unfinished 1996 manuscript),
section 1.1, printed/PDF pages 2–3. The source is registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
the PDF member has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The precise spectrum comparison and its proofs here are internal
consequences of the published bounded-seminorm pullback and restriction
constructions.

`spectrumFunctor_comp_groupForget` proves a strict equality of functors:
taking the spectrum and then retaining its topological operator group is
exactly the original quotient-action group functor. Both the groups and
their continuous homomorphisms are retained unchanged.

The existing `spectrumRestrictIso X f` identifies the actual spectrum of
the restricted algebra action with restriction of the continuous spectrum
action. Both directions have identity group maps and act as the identity
on actual bounded multiplicative seminorms. The comparison uses the group
homomorphism identity `f (h⁻¹) = (f h)⁻¹` to reconcile the inverse-pullback
spectrum action with restriction.

`spectrumFunctor_restrictionMap` proves equality of the complete arrows:
the spectrum of the canonical quotient restriction is the comparison
isomorphism followed by the canonical continuous-action restriction.
Extensionality proves the group components equal; extensionality on
seminorms proves the space components equal. No equality of restricted
action objects is asserted.

`spectrumFunctor_restrictionMap_isStronglyCartesian` proves that this actual
spectral arrow is strongly Cartesian for the continuous-action group
functor. The comparison is an isomorphism over the identity group map,
and the continuous restriction arrow is already strongly Cartesian.
Mathlib's composition theorem gives their strongly Cartesian composite,
which the complete-arrow comparison identifies with the spectral arrow.

For any actual continuous-action object `Z`, arrow
`h : Z → spectrumFunctor.obj X`, and group map `k : Z.groupType → H`
satisfying `f.comp k = h.groupHom`, `spectrumRestrictionLift f h k hgroup`
constructs a lift into `spectrumFunctor.obj (restrict X f)`. It first uses
the constructed continuous-action lift, then composes with the inverse
of the identity-on-seminorms comparison. Its group component is `k` and
its continuous space map is precisely the original space map of `h`.
The source `Z` need not be a quotient spectrum.

The full factorization is proved by extensionality of both arrow
components. Its group equation is the supplied compatibility equality;
evaluation on every algebra element identifies the composed seminorm
with the original one. A competing lift is determined by its prescribed group
component and its space component: evaluation of its factorization,
followed by the identity seminorm formula for canonical restriction,
recovers the original space map. This proves
`spectrumRestrictionLift_unique` and
`spectrumRestrictionLift_existsUnique`.

`spectrumFunctor_restrictionLift` proves that the spectrum of the existing
quotient lift equals this constructed continuous lift as a complete arrow.
The prescribed group maps agree and both space maps are the original
seminorm pullback along the quotient arrow's bounded algebra map.

The coefficient field is any ultrametric normed field in universe `u`;
operator groups have independent universe `v`. Every continuous group
homomorphism is allowed. These are actual quotient algebras and actual
continuous spectra, with their original norms and topologies. This module
does not construct full analytic atlases, the analytic automorphism
topology, étale morphisms, or sites, and does not identify norm-orbit
continuity with Berkovich's analytic continuity convention.
