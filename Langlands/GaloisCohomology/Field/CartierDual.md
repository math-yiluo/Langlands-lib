# The Cartier dual

`Langlands/GaloisCohomology/Field/CartierDual.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois module `M` over `Gal(L/K)`, its Cartier dual is `M' = Hom(M, Lˣ)` with the action
`(σ f)(m) = σ f(σ⁻¹ m)`, and the Cartier pairing `M × M' → Lˣ` is evaluation. For a finite module
whose exponent `n` has enough roots of unity in `L`, `M'` is `Hom(M, μ_n)`, has the same order as
`M`, and `M → M''` is an isomorphism; `(ℤ/n)' ≅ μ_n` and `μ_n' ≅ ℤ/n`. The Cartier dual is the
dual `dualRep` of `Langlands/Cohomology/Profinite/Duality/DualModule.lean` with values in the
units module, so the duality theorem there applies to it (local Tate duality is the case of a
local field).

## Declarations

- `cartierDual K L M` (`= dualRep (unitsModule K L) M`), `cartierDual_ρ_apply`,
  `coe_cartierDual_ρ_apply`; `cartierDualMap φ` (`= dualMap`, contravariant:
  `cartierDualMap_hom_apply`, `cartierDualMap_id`, `cartierDualMap_comp`) and the functor
  `cartierDualFunctor K L` (`cartierDualFunctor_obj`, `cartierDualFunctor_map`).
- `evalBilin K L M` (`= dualEvalBilin`), `cartierPairing K L M : M ⊗ M' ⟶ unitsModule K L`
  (`= evalPairing`; `cartierPairing_tmul`), `toCartierDualCartierDual K L M : M ⟶ M''`
  (`= toDualDual`; `toCartierDualCartierDual_hom_apply`).
- `cartierDualEquivMonoidHom K L M : M' ≃ (Multiplicative M →* Lˣ)` (`_apply`, `_symm_apply`).
- Roots of unity: `cartierDual_pow_eq_one` (values of `f ∈ M'` on `M` killed by `n` are `n`-th
  roots of unity), `bijective_ihom_map_rootsOfUnityToUnits`, `cartierDualIsoHomRootsOfUnityOfNsmul`,
  `cartierDualIsoHomRootsOfUnity` (`M' ≅ Hom(M, μ_n)`).
- Finiteness: instances `finite_cartierDual`, `finite_cartierDual_cartierDual`,
  `isSmoothRep_cartierDual` (from `isSmoothRep_dualRep`), `card_cartierDual` (`|M'| = |M|` when
  `L` has enough roots of unity of the exponent of `M`),
  `hasEnoughRootsOfUnity_exponent_of_isSepClosed`.
- `cartierPairingDiscrete K L M`: the Cartier pairing as a morphism of the Library's category
  `SmoothRep` (`cartierPairingDiscrete_hom`).
- Biduality: `eq_zero_of_forall_cartierDual_apply_eq_zero`, `exponent_cartierDual_dvd`,
  `hasEnoughRootsOfUnity_exponent_cartierDual`, `toCartierDualCartierDual_bijective`,
  `cartierBidualityIso`, `cartierBidualityIso_hom`, `cartierBidualityIsoOfIsSepClosed`.
- `cartierDualShortComplex K L S`: the dual of a short complex.
- `ℤ/n` and `μ_n`: `cartierDualZModHom`, `coe_cartierDualZModHom_hom_apply`,
  `cartierDualZModHom_bijective`, `cartierDualZModIso K L n : (ℤ/n)' ≅ μ_n`
  (`cartierDualZModIso_hom`), `cartierDualRootsOfUnityIso`, `cartierDualRootsOfUnityIsoOfIsSepClosed`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CartierDualDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/CartierDual.lean`. The repository has no licence file; its
text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

Names are the source's, with `galUnits` → `unitsModule`, `galRootsOfUnity` →
`rootsOfUnityModule`. Notions replaced: the source defines `cartierDual`, `cartierDualMap`,
`evalBilin`, `cartierPairing` and `toCartierDualCartierDual` directly; here they are
abbreviations of the general `dualRep`, `dualMap`, `dualEvalBilin`, `evalPairing`, `toDualDual`
of `Duality/DualModule.lean` with values in `unitsModule K L` (the same definitions), and the
source's general pieces (`Rep.isoOfBijective`, `zmodRep`, `uliftIntLinearEquivAddHom`,
`nsmul_zmodRep_eq_zero`, `exponent_zmodRep`, `finite_zmodRep`, `zmodRep_eq_zsmul`) are in that
file. The source's `cartierPairingDiscrete` into its category `DiscreteRep` is stated in the
Library's `SmoothRep`; the instance `isSmoothRep_cartierDual` is `isSmoothRep_dualRep`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter II, §5.2, Theorem 2, p. 91 (the dual module
  `A' = Hom(A, μ) = Hom(A, G_m)` of a finite `G_k`-module and the duality pairing).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VII, §2, Theorem (7.2.1), p. 379 (`A' = Hom(A, K^×)`), and
  Theorem (7.2.6), p. 380 (`A' = Hom(A, μ)` for a finite `G_k`-module).
