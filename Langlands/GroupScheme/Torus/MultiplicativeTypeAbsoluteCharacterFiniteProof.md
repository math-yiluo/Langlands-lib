# Finite generation of actual absolute-Galois characters

Authors: Worker 600 and Worker 3483. The Lean proof uses Worker 3483's
shared draft.

`Langlands.GroupScheme.multiplicativeTypeAbsoluteCharacterFinite` proves the
published proposition
`Langlands.GroupScheme.MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u}`
for every universe `u`. For any field `k : Type u` and any actual commutative
group scheme `T` over `Spec k`, the sole hypothesis is the existing
`IsMultiplicativeType T.toGrp`. The conclusion is `Module.Finite ℤ` for
the existing actual character group of `T` after base change to
`SeparableClosure k`.

The characters are actual group-scheme morphisms into the multiplicative
group, with the existing pointwise additive law and integer-module
structure. No rational-point replacement of that group is made. The result
retains arbitrary characteristic, torsion characters, and finite nonsmooth
groups of multiplicative type.

## Implemented proof

Unpack `IsMultiplicativeType` to obtain an arbitrary field extension `K/k`,
a finitely generated abelian group `M`, and an actual group-scheme
isomorphism `T_K ≅ D_K(M)`. Put `Ω = SeparableClosure k` and
`E = AlgebraicClosure K`. Since `Ω/k` is algebraic and `E` is an
algebraically closed extension of `k`, Mathlib's `IsAlgClosed.lift` gives
a `k`-algebra embedding `Ω → E`. Its induced algebra structure and
`IsScalarTower.of_algebraMap_eq'` make `k → Ω → E` a compatible tower.
The original tower `k → K → E` uses the canonical algebra structures.
All fields and the model group remain in `Type u`.

Let `TΩ` be the actual commutative base change of `T` to `Ω`, and `TΩE`
its further base change to `E`. Compose the inverse of
`baseChangeFieldTowerIso k Ω E T.toGrp`, the comparison through `K`,
the base change of the supplied splitting isomorphism, and
`Diagonalizable.baseChangeIso`. This yields

```text
TΩE.toGrp ≅ D_E(M).toGrp.
```

`DiagonalizableCharacter.evalCharacterEquiv E M` identifies `M` with the
full actual character group of `D_E(M)`. Compose with
`characterLattice.comapIso` for the displayed isomorphism. The resulting
additive equivalence from `M` onto `characterLattice TΩE` transfers finite
generation by `AddGroup.fg_of_surjective`. Convert this to `Module.Finite ℤ`
using `Module.Finite.iff_addGroup_fg`.

Finally, the canonical character base-change map from `TΩ` to `TΩE` is
injective by `characterLattice.algebraBaseChange_injective Ω E TΩ`.
That theorem uses faithful field pullback, with no separability or
smoothness restriction. View the additive map as an integer-linear map
and apply `Module.Finite.of_injective`. The noetherian property of `ℤ`
ensures that a submodule of the finitely generated target is finitely
generated. This proves precisely the required assertion for the actual
characters over `Ω`.

## Provenance and scope

The target isolates the finite-generation assertion in J. S. Milne,
*Algebraic Groups* (2017), §12.g and Theorem 12.23, printed pp.239–240 /
PDF pp.255–256. The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Those pages and the complete retained official 2017 errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` were read; no listed
correction changes the cited passages.

The implemented proof is an internal consequence of the published
diagonalizable evaluation and base-change comparisons, faithful character
base change, and Mathlib's field and noetherian-module results. It uses
the original arbitrary splitting extension and does not invoke the
categorical classification theorem as a proof. Finite or separable
splitting, group smoothness, connectedness, freeness, torsion-freeness
and characteristic restrictions are not additional hypotheses.
Continuity of the canonical absolute-Galois action, finite Galois
splitting, and the categorical anti-equivalence remain separate results.
