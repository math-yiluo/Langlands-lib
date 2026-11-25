# A closed birational morphism is an isomorphism over a dense open

Module `StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Tag 0BAC gives, for a birational morphism `f : X ⟶ Y` between schemes with finitely many irreducible components and under a finiteness hypothesis, dense opens `U ⊆ X` and `V ⊆ Y` with `f` restricting to an isomorphism `U ≅ V`. This file upgrades that to an isomorphism over a dense open of the target, that is, a dense open `W ⊆ Y` with `f⁻¹(W) → W` an isomorphism, when `f` is closed.

## Results

All three assume that `X` and `Y` have finitely many irreducible components and that `f` is birational (`IsBirational`).

- `preimage_genericPoints_eq_genericPoints_of_isBirational`: the preimage of the set of generic points of `Y` is the set of generic points of `X`.
- `exists_dense_open_isIso_morphismRestrict_of_isClosedMap`: if moreover `f` is closed on underlying spaces and either `f` is locally of finite type with `Y` reduced, or `f` is locally of finite presentation, there is a dense open `W ⊆ Y` with `f ∣_ W` an isomorphism.
- `exists_dense_open_isIso_morphismRestrict_of_isIntegralHom`: the same for `f` integral, which is universally closed.

## Proof

Starting from the isomorphism `U ≅ V` of Tag 0BAC, take `W = V` minus the image of the complement of `U`; it is open because `f` is closed. It is dense because it contains every generic point of `Y`, using the first result and the fact that a dense open of a space with finitely many irreducible components contains all generic points.

## Watch for

- The statements are not Tag 0BAJ, though they reach a similar conclusion: they replace the hypothesis "quasi-compact or separated" of that tag by "closed", which is neither weaker nor stronger, and they are deliberately not tagged.
- `IsBirational` is the library's own predicate, not Mathlib's; the proofs use that it makes `f` a bijection from the generic points of `X` onto those of `Y` (`hf.bijOn`).

## References

Tag 0BAC, Tag 0BAJ, Tag 0BAI.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/BirationalDenseOpenIso/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
