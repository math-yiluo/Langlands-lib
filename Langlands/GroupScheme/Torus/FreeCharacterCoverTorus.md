# Diagonalizable groups with free character group, and the free cover embedding

All schemes lie in an arbitrary universe `u`. Here `diagonalizable X Λ` is the
published `D_X(Λ)`, the base change of `D(Λ) = Spec ℤ[Λ]` from `Spec ℤ`.
`diagonalizableMap X g : D_X(Λ) ⟶ D_X(Λ')` is the homomorphism induced by an
additive map `g : Λ' →+ Λ` (module `RelativeDiagonalizableHomLocality`).

- `isSplitTorus_diagonalizable`: if `Λ` is a finite free ℤ-module, then
  `D_X(Λ)` is a split torus. A chosen basis gives `Λ ≃+ (ι → ℤ)` with `ι`
  finite. The published `Diagonalizable.isSplitTorus` says that `D(Λ)` over
  `Spec ℤ` is split, and being split is preserved by base change to `X`.
- `isClosedSubgroup_diagonalizableMap`: if `g : Λ' →+ Λ` is surjective, then
  `diagonalizableMap X g` is a closed immersion (`IsClosedSubgroup`). The
  published `Diagonalizable.isClosedImmersion_restrictMap` proves this over
  `Spec ℤ`, since `ℤ[Λ'] → ℤ[Λ]` is surjective, and base change to `X`
  preserves it (`IsClosedSubgroup.baseChange`).
- `isSplitTorus_diagonalizable_cover`: for finitely generated `Λ`, the group
  `D_X(F(Λ))` of the free cover `F(Λ) = FreeCharacterCover.Cover Λ` (module
  `FreeCharacterCover`) is a split torus, because `F(Λ)` is finite free.
- `isClosedSubgroup_diagonalizableMap_proj`: the homomorphism
  `D_X(Λ) ⟶ D_X(F(Λ))` induced by the surjection
  `FreeCharacterCover.proj Λ : F(Λ) → Λ` is a closed immersion.

Together these give, on each chart, the closed embedding of a diagonalizable
group into a split torus that Conrad, *Reductive group schemes* (2014), uses in
the proof of Proposition B.3.8. Provenance: these are direct consequences of
the published diagonalizable-group API. There is no new literature assertion.

The general `isClosedSubgroup_diagonalizableMap` theorem is reused from [`RelativeDiagonalizableExactQuotient`](RelativeDiagonalizableExactQuotient.md). This module supplies its free-cover specialization.
