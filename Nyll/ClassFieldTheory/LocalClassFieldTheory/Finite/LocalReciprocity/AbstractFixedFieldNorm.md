# Abstract norms and field norms for fixed fields of closed subgroups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's abstract class-formation framework indexes fields by closed subgroups `H` of `Gal(Ω / K)`, while local norm computations concern the concrete fixed fields `E = abstractFixedField K Ω H`. This file identifies the abstract norm `normToBase` on `H`-fixed units with the field norm from `E` to `K`, and from this computes the image of the base valuation after the norm. Normality of `E` over `K` is not assumed.

## Main results

- `relativeNorm_coe_eq_of_closedSubgroup_eq`: a transport lemma, for a group `G : Type` with a topology, a representation `A : Rep ℤ G` and finite quotients on both sides: the underlying value of `relativeNorm A B C hCB x` is unchanged when `B`, `C` and `x` are replaced by equal data.
- `normToBase_abstractFixedFieldUnit_val_of_isSeparable`: let `Ω` be Galois and separably closed over `K`, `H` a closed subgroup of finite index, and `E` finite-dimensional and separable over `K`. For a unit `x` of `E`, the abstract norm of the fixed coefficient corresponding to `x` has underlying element `algebraMap K Ω (Algebra.norm K x)`.
- `localBaseValuation_normToBase_abstractFixedFieldUnit`: for a nonarchimedean local field `K` and `Ω = SeparableClosure K`, the base valuation `localBaseValuation K` (with values in `ℤ̂`) of this abstract norm is the image in `ℤ̂` of the valuation `valuationMap K` of the norm `normUnits K E x`.
- `localBaseValuation_comp_normToBase_range_eq_residueFinrank`: under further hypotheses on `E` (below), the range of the base valuation composed with `normToBase` is `f` times the range of the base valuation, where `f = [k_E : k_K]` is the residue degree, written with `nsmulImage`.

## Proofs

The first identification combines `relativeNorm_intermediateFieldUnit_val_of_isSeparable` for intermediate fields with the transport lemma and `closedFixingSubgroup_abstractFixedField_eq`. The range statement rests on `v_normUnits_eq_residue_finrank_mul_of_isSeparable`, giving `v_K(N x) = f · v_E(x)`, and on surjectivity of `v_E`.

## Points to watch

- The range theorem takes as instance hypotheses on `E` a valuative relation, a topology, the structure of a nonarchimedean local field, `Valuation.HasExtension` from the valuation of `K`, and `IsIntegralClosure 𝒪[E] 𝒪[K] E`. They are not derived here from `E ⊆ SeparableClosure K`.
- The generic norm identification asks for separability of `E / K` explicitly; the two local statements do not list it.
- Everything is in universe `0`: the generic norm identification takes `K Ω : Type`, the local statements `K : Type`. The base valuation of the local statements is `ℤ̂`-valued, so the results compare integer valuations through `Int.castRingHom ZHat`.
- A local instance `fixedFieldNormResidueModule` provides the module structure of one residue field over another.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`: the Lean file is the source byte for byte (SHA-256 `6e8d9eb2a8c4d487b2a40862bda695366e47cc021968af1ef7abbd1d4225f4c3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
