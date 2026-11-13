# Brauer-kernel compatibility from the global argument

Author: Worker 5093. This unit assembles Deligne's global argument (P. Deligne, *Les constantes
des équations fonctionnelles des fonctions L*, 1973, proof of Lemma 4.12) for
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`, the target of task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`. Its final theorem takes one hypothesis, the published
statement

- `hN3 : LocalTransferReciprocityStatement.{0}` (Tate 1979, (1.6.1) for local maps into relative
  Weil groups).

The module `Langlands.LocalFactor.NonabelianBrauerKernelProof` discharges it with the published
theorem `ClassField.Global.RelativeWeilGroup.localTransferReciprocity`. All other inputs are
proved Library results. In particular, the existence of normalized common-closure reciprocity
families is the published theorem `LocalClassField.commonClosureReciprocityExistence`
(`Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof`), the transfer reciprocity of
p-adic extensions is `LocalClassField.extensionWeilTransferReciprocity`
(`Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`), the existence of
local-to-relative Weil maps is the published theorem `localRelativeWeilMapExistence`
(`Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof`), and the dimension identity
`globalField_type_dimension` is Worker 126's published unit
`Langlands.LocalFactor.BrauerKernel.GlobalDimension`.

## Results

- `evaluationMap_eq_zero_bottom`: given `hCC : LocalClassField.CommonClosureReciprocityExistence`,
  `hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement`, `hN3` and the existence
  statement `hM : LocalRelativeWeilMapExistenceStatement`, every presentation `z` over the
  bottom field with `presentationMap z = 0` has `evaluationMap F _ ψ' measures z = 0`, for every
  additive character `ψ'` and Haar family. Proof:
  1. Decompose `z` by Galois types (`nonempty_galoisTypeDecomposition`, with normal field `D.K`).
     `D.K / F` is Galois: it is normal, and separable in characteristic zero.
  2. Realize `D.K / F` as `K'_w / k_v` for a totally real Galois extension `K'/k`, with `w` the
     only place above `v` (the proved `totallyRealGaloisRealization`). Identify `p` with the
     residue prime of `v` (`residuePrime_eq_of_ringEquiv`) and substitute.
  3. Take the local invariant families (`localAbsoluteCorestrictionCompatibleClassFormation`) and
     the global class family `c` (`globalFundamentalClassStatement`). Write the inflated
     characters of `D.θ_j g` as reciprocity characters of Hecke characters `Θ_j g`
     (`transferCharacterFactorization`, `exists_eq_continuousReciprocityCharacter`).
  4. Enumerate the support of `z`. Apply `exists_twist_placeEpsilonRatioProduct_eq_one` (unit
     `GlobalCore`). Its global relation is `globalRelation_generatorHecke` (unit
     `GlobalCharacters`), its archimedean triviality is `globalCharacter_inclusion`, and its
     balancing is `globalField_type_dimension`.
  5. `evaluationMap_eq_zero_of_placeEpsilon` (unit `GlobalAtV`) gives the vanishing for the base
     character `baseFieldAdditiveCharacterEquiv F ψF` of the transported `ψv`.
     `evaluationMap_additiveCharacter_independent` transfers it to `ψ'`.
- `kernelCompatibilityStatement_of_localTransferReciprocity`: the hypothesis `hN3` implies
  `KernelCompatibilityStatement.{uF, uV}`. Proof: `evaluationMap_eq_zero_of_bottom` (published
  unit `BottomReduction`) reduces an arbitrary extension to the bottom field, and the previous
  item handles the bottom field, with `hCC` discharged by `commonClosureReciprocityExistence`,
  `hsq` by `extensionWeilTransferReciprocity` and `hM` by `localRelativeWeilMapExistence`.

Both theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
