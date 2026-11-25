# Abstract unramified extensions and their ramification groups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the library's class-formation approach to local class field theory, unramified extensions of a nonarchimedean local field `K` are described abstractly, through the residue-degree datum `localResidueDatum K` on the absolute Galois group. This file shows that an abstractly unramified, normal, finite fixed field `E ⊆ SeparableClosure K` is unramified in the concrete sense for its valuation, and deduces that its upper ramification groups vanish. The header describes it as the bridge to the Hasse–Arf development.

## Main definitions and results

- `finiteAbstractField_residueDegree_eq_relativeResidueDegree`: for any degree data on a group, the absolute residue degree of a field finite over the base equals its relative residue degree over the base.
- `finiteAbstractField_degree_eq_abstractFixedField_finrank`: for any field `K` and a finite abstract field `H` normal over the base, its abstract degree is `[E : K]`, where `E` is the fixed field of `H`.
- `abstractFixedField_isUnramifiedValuedExtension`: for `K` a nonarchimedean local field and `H` normal and abstractly unramified (hypotheses `hnormal`, `hunramified`), `E` with its spectral valuation is an unramified valued extension of `K` (`IsUnramifiedValuedExtension`).
- `localUpperRamificationGroup_abstractFixedField_eq_bot`: under the same hypotheses, `localUpperRamificationGroup K E t = ⊥` for every real `t ≥ 0`.
- `localFiniteUnramifiedAbstractField K d hd`, for a natural number `d` with `hd : 0 < d`: the canonical degree-`d` unramified factor as an abstract field finite over the base, with `localFiniteUnramifiedAbstractField_field`, `localFiniteUnramifiedAbstractField_normal` and `localFiniteUnramifiedAbstractField_isUnramified`.
- `localUpperRamificationGroup_finiteUnramifiedAbelianExtension_eq_bot`: the upper ramification groups of this canonical factor vanish for `t ≥ 0`.
- `artinPrincipalUnitStepGroup_finiteUnramifiedAbelianExtension_eq_bot`: the library's Artin principal-unit step group of this factor is trivial for every real `t`.

## Proof

The residue degree `f` of `E / K` equals the abstract residue degree (`localResidueDatum_residueDegree_eq_residueFinrank`), which equals the abstract degree because `E` is unramified, hence equals `[E : K]`. Combined with `e · f = [E : K]`, obtained from `maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure` after private lemmas reconcile two module structures on the residue field, this gives `e = 1`. The vanishing results then follow from `localUpperRamificationGroup_eq_bot_of_unramifiedValuation` and `artinPrincipalUnitStepGroup_eq_bot_of_unramifiedValuation`.

## Points to watch

- The valuation on `E` is a specific one: the spectral norm and valuation (`finiteExtensionSpectralNormedField`, `finiteExtensionSpectralValuativeRel` and related instances), installed by `let` inside the statement of `abstractFixedField_isUnramifiedValuedExtension`, whose conclusion concerns that structure. The vanishing results do not carry it in their statements: it is installed inside the proofs.
- `localUpperRamificationGroup` and `artinPrincipalUnitStepGroup` are the library's own definitions, not Mathlib's.
- The upper-ramification statements cover only `t ≥ 0`; the Artin step statement covers every `t`.
- For a general `H`, normality and unramifiedness are hypotheses; they are proved here only for the canonical factor.
- The degree comparison `finiteAbstractField_degree_eq_abstractFixedField_finrank` and the local statements take `K : Type` in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `bbd3057fa39260bd1b64688c8547b2a6704c0125c11843077dd52fc649bb39d4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
