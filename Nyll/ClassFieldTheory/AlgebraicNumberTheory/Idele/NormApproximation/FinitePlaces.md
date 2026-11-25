# Weak approximation modulo local norm groups at finite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, L/K a finite Galois extension and S a finite set of finite places of K. For each v ∈ S the file chooses an extension w of the v-adic absolute value to L and forms the local extension L_w/K_v. It then transports the norm subgroup N(L_wˣ) to Mathlib's adic completion of K at v, which the idele library uses. These subgroups are open, so weak approximation makes the diagonal map from Kˣ to the product over v ∈ S of the quotients K_vˣ / N(L_wˣ) surjective.

## Main definitions and results

- `finitePlaceCompletionRingEquiv`, `finitePlaceCompletionContinuousMulEquiv` and `finitePlaceCompletionUnitsContinuousMulEquiv` identify the completion of K for the absolute value `adicAbv K v` with `v.adicCompletion K`: as rings, topologically, and on unit groups. The map extends the isometric embedding of K. It is onto because its range is closed and contains the dense image of K.
- `chosenFinitePlaceExtension`: an extension of `adicAbv K v` to L, obtained by embedding L into an algebraic closure of the completion (`IsAlgClosed.lift`). `ChosenFinitePlaceLocalizedCompletion` is the resulting local field L_w.
- `chosenFinitePlaceLocalNormSubgroup`: the norm subgroup of L_w/K_v, transported into `(v.adicCompletion K)ˣ`.
- `chosenFinitePlaceLocalNormSubgroup_isOpen`: this subgroup is open.
- `ChosenFinitePlaceNormQuotient` is the quotient of the concrete unit group, and `ChosenFinitePlaceIntrinsicNormQuotient` is the `NormQuotient` used by local class field theory. They are compared by `chosenFinitePlaceNormQuotientEquiv`, and over all of S by `chosenFinitePlaceNormQuotientFamilyEquiv`.
- `principalLocalNormQuotientMap S`: the diagonal map from Kˣ to the product over S of the concrete quotients.
- `principalLocalNormQuotientMap_surjective`: this map is surjective. `principalIntrinsicLocalNormQuotientMap_surjective` gives the same in the intrinsic model.
- `mem_ker_principalLocalNormQuotientMap_iff` and `principalLocalNormQuotientMap_ker`: x is in the kernel if and only if it is a local norm at every v ∈ S. The kernel is the intersection of the pullbacks of the local norm subgroups.

## Proofs

Openness comes from the local theorem `localNormSubgroup_isOpen`, once the completion has been given the structure of a nonarchimedean local field (locally compact, ultrametric, nontrivially valued). Surjectivity is the imported `IdeleGroup.principalLocalQuotientMap_surjective`, applied to these open subgroups.

## Points to watch

- At each v, the norm subgroup is defined from a single extension w, chosen through `IsAlgClosed.lift`. The file does not compare different choices of w.
- The local norm group is that of one completion L_w, not of the algebra K_v ⊗_K L.
- Only finite places occur in S.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormApproximation/FinitePlaces.lean`: the Lean file is the source byte for byte (SHA-256 `cea61d583092154958962cd11bb64767b2628df8d1431dedee9d8e65340862ab`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
