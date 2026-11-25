# Open subgroups of the absolute Galois group and finite subextensions

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file develops the Galois correspondence at finite level for `G_K = Gal(K^al/K)`, where `K^al` is Mathlib's `AlgebraicClosure K`. Finite intermediate fields correspond to open subgroups, and normal ones to open normal subgroups. Several natural maps are shown to be Krull continuous.

## Continuity in the Krull topology

- `semilinear_conjugation_continuous`: let `e : Ω ≃ Ω'` be a ring isomorphism compatible with a field isomorphism `F ≃ F'`. A homomorphism `Gal(Ω/F) → Gal(Ω'/F')` that acts by `g ↦ e g e⁻¹` is continuous; `algEquiv_autCongr_continuous` is the case of an `F`-algebra isomorphism.
- `separableClosureContinuousMulEquiv`: restriction gives an isomorphism of topological groups `Gal(K^al/K) ≃ Gal(K^sep/K)`. Its inverse extends uniquely, because `K^al` is purely inseparable over `K^sep`.
- `ofIntermediateFieldInExtension` and `ofIntermediateField`: the inclusion `Gal(M/E) → Gal(M/K)`, with image the subgroup fixing `E` and continuous when `E / K` is finite (the first also assumes `IsGalois K M`). `restrictNormalHom_ker_eq_range_ofIntermediateFieldInExtension` gives exactness `Gal(M/E) → Gal(M/K) → Gal(E/K)` for normal `E`.

## Finite subextensions and open subgroups

- `openSubgroupOfFiniteIntermediateField K E`: the subgroup fixing a finite `E`, as an open subgroup. It reverses inclusions, sends `E ⊔ F` to the intersection, and is isomorphic to `Gal(K^al/E)` as a topological group. `openSubgroupOfNormalClosureFiniteIntermediateField` is the version for the normal closure; it is normal and of finite index equal to the order of the Galois group of the normal closure.
- `quotientEquivGalOfNormalIntermediateField`: `G_K / G_E ≃ Gal(E/K)` for normal `E`.
- `fixedFieldOfOpenSubgroup`: the fixed field of an open subgroup. Assuming `IsGalois K K^al`, it is finite over `K`, and the two constructions are mutually inverse and order-reversing. Intersections of open subgroups go to composita and generated subgroups to intersections of fields. The index of the open subgroup attached to `E` is `[E : K]`.
- `conjugateOpenSubgroupOfOpenSubgroup σ H`: defined as the open subgroup of `σ((K^al)^H)`. `…_toSubgroup` shows it equals `σHσ⁻¹`, and it commutes with `⊓` and `⊔`.
- `openNormalCoreOfOpenSubgroup`: the normal core of an open subgroup, which is open and normal. Its fixed field is the normal closure of `(K^al)^H` (`fixedFieldOfOpenNormalCoreOfOpenSubgroup`), and is unchanged when `H` is conjugated.
- `quotientOpenNormalSubgroupEquivGalFixedField`: for an open normal `H`, `G_K / H ≃ Gal((K^al)^H/K)`, and `(K^al)^H / K` is finite Galois.

## Proofs

Continuity is checked at the identity through fixing subgroups of finite subfields. The correspondence applies Mathlib's infinite Galois theory to open subgroups.

## Watch for

- Most of the correspondence assumes `IsGalois K (AlgebraicClosure K)` as an explicit hypothesis. The file notes it is automatic in characteristic zero. It fails for imperfect `K`, where those results do not apply.
- `conjugateOpenSubgroupOfOpenSubgroup` is defined through fixed fields. It agrees with pointwise conjugation only by a theorem that needs this hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean`: the Lean file is the source byte for byte (SHA-256 `d23a0d69b5d2e1cd5ef16616ab4db4a6ff154772df4290fe39ccff5af920edee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
