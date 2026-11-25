# A finite support for the idele-class Herbrand calculation

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields. The file builds the finite set of finite places of `K` used for the Herbrand-quotient calculation of the idele class group: it contains the places below a sufficiently large set of places of `L` and every place of `K` with a ramified prime above it. Along the way it compares the relative ideles supported at a set `S` of places of `K` (defined through the local tensor coordinates) with the ordinary ideles of `L` supported above `S`.

## Main declarations

- `finitePlacesAbove S`: the finite places of `L` lying above a finite set `S` of finite places of `K`. It is stable under `L ≃ₐ[K] L` (`finitePlacesAbove_isGaloisStable`), because conjugation does not change the place below (`finitePlaceBelow_finitePlaceEquiv`).
- `principalIdele_mem_supportedAt_iff_sUnit`: the principal idele of `x ∈ Lˣ` is a unit at every finite place outside `T` exactly when `x` lies in the `T`-unit group `SUnitGroup T`.
- `relativeIdeleBaseChange_mem_supportedAt_iff` and its subgroup form `relativeIdeleLocalTensorDecompositionSupportedSubgroup_map_baseChange`: under the isomorphism `relativeIdeleBaseChangeMulEquiv` from relative ideles to the ideles of `L`, the relative subgroup supported at `S` corresponds exactly to the ideles of `L` supported at `finitePlacesAbove S`.
- `relativeIdeleSupported_sup_principal_eq_top`: if the supported ideles above `S` and the principal ideles generate the idele group of `L`, the same holds for their relative counterparts.
- `sUnitEquivRelativePrincipalSupportedIntersection`: the `S`-units of `L` (for the places above `S`) are isomorphic to the relative principal ideles inside the relative supported subgroup; `relativePrincipalSupportedIntersectionAction` is the Galois action on the latter, and `sUnitEquivRelativePrincipalSupportedIntersection_smul` states equivariance.
- `ramifiedBaseFinitePlaces`: finite places `v` of `K` with a prime of `𝓞 L` over `v` that is not unramified (`Algebra.IsUnramifiedAt`).
- `ideleClassHerbrandSupport`: the image of `IdeleGroup.sufficientlyLargeFiniteSet` of `L` under `finitePlaceBelow`, union `ramifiedBaseFinitePlaces`.
- `supportedAboveHerbrandSupport_sup_principal_eq_top` and `relativeSupportedAboveHerbrandSupport_sup_principal_eq_top`: for this support, supported and principal ideles generate the whole idele group, for `L` and in the relative model.
- `isUnramifiedAt_of_notMem_ideleClassHerbrandSupport`: every finite prime of `L` above a place outside the support is unramified.

The relative statements are transported through `relativeIdeleBaseChangeMulEquiv`; the generation statement for `L` follows from `IdeleGroup.supportedAt_sup_principalSubgroup_eq_top`.

## Points to watch

- `relativeIdeleSupported_sup_principal_eq_top` takes the generation statement for `I_L` as a hypothesis (`hOrdinary`); it is discharged here only for `ideleClassHerbrandSupport`.
- The support depends on the library's choice `IdeleGroup.sufficientlyLargeFiniteSet`. Ramification concerns finite primes only; infinite places are not in `S`.
- The relative statements are stated for `K L : Type`, while the others allow arbitrary universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SupportedBridge.lean`: the Lean file is the source byte for byte (SHA-256 `5bcefabaa5689d96d1dacde2d414707730f3afb17af2a9523db7c581735485ba`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
