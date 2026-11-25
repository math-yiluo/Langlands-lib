# The degree formula ∑ e_w f_w = [L : K] for discrete absolute values

Module `Nyll.ValuedFieldTheory.Valuation.Completion.ExtensionInvariants`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite separable extension `L / K` and a nonarchimedean absolute value `a` on `K` whose exponential valuation `−log a` is discrete, the file proves that the sum of `e_w f_w` over all absolute values `w` on `L` extending `a` equals `[L : K]`. On the way it shows that metric completion keeps the value group and the residue field, and that each completed extension `L_w / K_v` is finite separable.

## Main results

- `completionNonarchimedean`: the completion of a nonarchimedean absolute value is nonarchimedean.
- `completionExponentialValueSubgroup_eq`, `completionRamificationIndex_eq`: completion does not change the value group, hence not the ramification index.
- `completionExponentialSubringMap`, `completionResidueEquiv`: the map from the valuation ring `{a ≤ 1}` of `K` to that of its completion is a local homomorphism, and it induces a ring isomorphism of residue fields (by density, the residue map is surjective). `completionResidueDegree_eq` deduces that completion does not change the residue degree.
- `completionExponentialValuation_discrete`: discreteness passes to the completion.
- `completionExtension_isSeparable`: for `L / K` finite separable, `a` nontrivial and `w` extending `a`, the completion of `L` at `w` is separable over the completion of `K`.
- `completionExtensionInvariants_local_identity`: under the discreteness hypothesis, `[L_w : K_v] = e_w f_w`.
- `absoluteValue_isNontrivial_of_discrete`: if the exponential valuation of `a` is discrete, then `a` is nontrivial.
- `completionExtensionInvariants`: the global formula `∑_w e_w f_w = [L : K]`.

## Proofs

Separability: a primitive element `α` of `L / K` is sent to a root of an irreducible factor, over the completion, of the minimal polynomial of `α`, and that factor is separable. The local identity applies a fundamental identity for discrete Henselian valuations (proved elsewhere in the library) to the completed extension, which is Henselian because it is complete, and then transports `e` and `f` back with the invariance results. The global formula substitutes the local identity into the library's degree formula `∑_w [L_w : K_v] = [L : K]`.

## Points to watch

- The sum runs over the type `AbsoluteValueExtension a L` of real absolute values on `L` that extend `a` exactly, not over equivalence classes of places; it is made finite by an instance from the tensor product decomposition.
- "Nonarchimedean" is the library's predicate `LubinTate.Valuations.NonarchimedeanAbsoluteValue`, a boundedness condition on the values at integers; it is converted to the ultrametric inequality through Mathlib.
- `e` and `f` are the library's `exponentialRamificationIndex` and `exponentialResidueDegree`, defined through the exponential valuation `−log a`, its value group and its valuation ring `{a ≤ 1}`.
- Discreteness is the library's `DiscreteExponentialValuation`: the values of nonzero elements are integer multiples of some `s > 0`, and `s` is attained.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/ExtensionInvariants.lean`: the Lean file is the source byte for byte (SHA-256 `dba3301f5fcbbf89db1042943a6b0262ee0a435d1e8136738e734a60cab9f6db`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
