# Idele norms under extension of scalars

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ExtensionBehavior`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, and let `IdeleGroup.extension K L` be the map from the ideles of K to the ideles of L. This file proves that this map raises the archimedean and the absolute idele norms to the power [L : K]. It also records a statement for ℚ that the module comment ties to cyclotomic reciprocity.

## Main results

- `IdeleGroup.archimedeanNorm_extension`: for an idele a of K, the archimedean norm of `extension K L a` is the archimedean norm of a raised to the power [L : K].
- `IdeleGroup.absoluteNorm_extension`: `absoluteNorm (extension K L a) = absoluteNorm a ^ [L : K]`. It combines the archimedean result with `finiteAbsoluteNorm_extension` from the imported file on the finite part.
- `IdeleGroup.absoluteNorm_relativeIdeleBaseChange_inclusion_of_finite_eq_one`: let a be an idele of ℚ whose finite part is 1. Take its image under `RelativeIdeleGroup.inclusion ℚ L` followed by `relativeIdeleBaseChangeMulEquiv`. That image has absolute norm `absoluteNorm a ^ [L : ℚ]`.

## Proof

The private helper lemmas establish three facts:

- the completion map from K_v to L_W, for W over v, is an isometry;
- the multiplicity m_W equals m_v times the local inertia degree;
- summed over the places W above v, the m_W give m_v · [L : K], because the inertia degrees add up to [L : K] (`InfinitePlace.sum_inertiaDeg_eq_finrank`).

The archimedean norm of the extended idele is then regrouped over the fibres of the map from places of L to places of K, and the multiplicities are summed.

## Points to watch

- `extension`, `archimedeanNorm` and `absoluteNorm` are the library's own definitions. Its absolute norm is the reciprocal of the usual ∏_v |a_v|_v, which does not affect these power identities.
- The proof of the ℚ statement identifies its left side with `absoluteNorm (extension ℚ L a)`. The statement therefore also follows from `absoluteNorm_extension`, without the hypothesis on the finite part.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/ExtensionBehavior.lean`: the Lean file is the source byte for byte (SHA-256 `1a626c43e43e2f476ecbd6d1a2507a730eb7f08c1c700b8c8bdcab6ae7fe321c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
