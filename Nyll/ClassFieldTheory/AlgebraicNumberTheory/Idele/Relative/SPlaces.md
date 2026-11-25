# S-integral subgroups of the relative idele group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, the library's relative idele group `RelativeIdeleGroup K L`, built on `𝔸_K ⊗[K] L`, has a component in `(K_w ⊗[K] L)ˣ` at every place `w` of `K`. This file defines, for a finite set `S` of finite places of `K`, the subgroup of relative ideles that are integral units outside `S`, describes it as an explicit product of local factors, and equips everything with the action of `Gal(L/K) = L ≃ₐ[K] L`.

## Main definitions and results

- `relativeIdeleLocalTensorDecompositionSupportedSubgroup S`: relative ideles whose finite component at every `w ∉ S` lies in `relativeLocalTensorDecompositionIntegralUnitSubgroup w`, the units of `K_w ⊗[K] L` that are valuation-ring units in each completion of `L` above `w`. Its membership criterion is a simp lemma; it grows with `S`.
- `relativeIdele_mem_localTensorDecompositionSupportedSubgroup`: each idele lies in the subgroup for its own support set, so `iSup_relativeIdeleLocalTensorDecompositionSupportedSubgroup_eq_top` shows the subgroups exhaust the group.
- `RelativeIdeleSPlaceFactors S`: the product of all archimedean factors `(K_v ⊗[K] L)ˣ`, the unrestricted factors at `w ∈ S`, and the integral-unit subgroups at `w ∉ S`. `relativeIdeleSPlaceFactorsEquivLocalTensorDecomposition` leaves the archimedean factors unchanged and rewrites each finite factor as a product of unit groups (valuation-ring unit groups outside `S`) of the completions of `L` above `w`.
- `relativeIdeleSupportedEquivSPlaceFactors`: the multiplicative isomorphism between the supported subgroup and `RelativeIdeleSPlaceFactors S`, built from the component map `relativeIdeleSupportedComponents` and its injectivity and surjectivity.
- `relativeIdeleLocalTensorDecompositionSupportedSubgroupAction` and `relativeIdeleSPlaceFactorsAction`: the Galois action restricted to the supported subgroup and the coordinatewise action on the factor model; `relativeIdeleSupportedComponents_smul` shows the component map is equivariant.

## Proof

Surjectivity assembles prescribed factors into local idele data (`relativeLocalIdeleDataOfSPlaceFactors`), which must have coefficients, in a chosen `K`-basis of `L`, integral at almost all places. Outside `S` together with the finite set `integralTensorComparisonBadPlaces`, an imported lemma turns local integral units into basis-integral units.

## Points to watch

- The relative idele group is the library's own construction. Integrality in the chosen basis and the integrality used for the supported subgroups are different notions; they are compared only outside a finite set of bad places, by an imported lemma.
- `S` contains only finite places; the archimedean factors are never restricted.
- Only the component map is shown equivariant. Equivariance of the rewriting into completions of `L` is not stated.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Relative/SPlaces.lean`: the Lean file is the source byte for byte (SHA-256 `6ce50e7643268b1e642cdc7056896dd31d6e3b308550210b8a6556db78359c79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
