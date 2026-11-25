# Residue actions under the field-of-norms correspondence

Module `Langlands.LocalFactor.Ramification.Wintenberger.NormFieldResidue`, namespace
`Langlands.Ramification.Wintenberger`.

Let `K` be a field of `FontaineWintenberger.IsPerfectResidueLocalField`, `L/K` an infinite
separable arithmetically profinite extension, `Ω` a separable closure of `K` and of `L`, and
`U = RelFieldOfNorms K L Ω` the relative field of norms. An automorphism `a` of `Ω` over `L`
corresponds to the automorphism `RelFieldOfNorms.autEquiv K L Ω a` of `U` (Wintenberger,
Corollaire 3.2.3). This file shows that if `a` acts on the residue field of `Ω` as an integral
power of the `q`-power map, so does the corresponding automorphism of `U` on its residue field,
and deduces that residue degrees correspond. The hypotheses on `X'`, `hbij` and `hval` are those of
`Wintenberger.NormField`: `X'` is a Mathlib nonarchimedean local field identified with the field of
norms `X_K(L)`, compatibly with the valuations.

## Main statements

- `exists_mem_stageImage (x : U) : ∃ N, x ∈ stageImage K L Ω N`: every element of `U` lies in the
  norm field of a finite Galois stage.
- `stageIntegersAlgebra K L Ω N`: the integers of `K` act on an intermediate field `N` through `K`
  (`Algebra.ofSubsemiring`), installed as a high-priority local instance;
  `integralClosure_isLocalRing'`: the integral closure of the integers of `K` in an algebraic
  extension is a local ring.
- `algebraicResidueAut_stage_isFrobPow (a : Ω ≃ₐ[L] Ω)
  (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q M) (N) :
  IsFrobPow (FontaineWintenberger.algebraicResidueAut K N ((a.restrictNormal N).restrictScalars K))
  q M`, with `N = (galoisStage L Ω N).val`.
- `autEquiv_of_galoisStage (τ) (N) (x)`: on the norm field of a finite Galois stage,
  `RelFieldOfNorms.autEquiv K L Ω τ` acts as `FieldOfNorms.autEquiv K L N (τ.restrictNormal N)`.
- `stageSpectralEquiv K L Ω X' hbij N`: the FontaineWintenberger spectral integers and the Library's
  `LocalGalois.extensionIntegers` of a stage over `X'` are the same ring.
- `relFieldOfNorms_residueHom_isFrobPow (a : Ω ≃ₐ[L] Ω)
  (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q M) :
  IsFrobPow (LocalGalois.residueHom X' U ((RelFieldOfNorms.autEquiv K L Ω a).restrictScalars X'))
  q M`.
- `relFieldOfNorms_localResidueDegree (Ω') [Algebra.IsAlgebraic X' Ω'] [IsSepClosed Ω']
  (e : U ≃ₐ[X'] Ω') (a : Ω ≃ₐ[L] Ω) (n : ℤ)
  (hq : Nat.card (Weil.Local.SepClosed.localResidueField X') = q)
  (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q (-n)) :
  Weil.Local.SepClosed.localResidueDegree X' Ω'
  (e.autCongr ((RelFieldOfNorms.autEquiv K L Ω a).restrictScalars X')) =
  Weil.frobenius (Multiplicative.ofAdd n)`.

## Proofs

A residue class of `U` is represented by an integer `x` of a stage `X_K(N)` with `N/L` finite
Galois (`exists_mem_stageImage`). The residue field of the valuation ring of `X_K(N)` is that of
the integral closure of the integers of `K` in `N` (`FieldOfNorms.residueEquiv`), compatibly with
the automorphisms (`FieldOfNorms.residueAut_residueEquiv`), and the residue action of `a` on `Ω`
restricts to `N` through the inclusion of residue fields
(`integralClosureResidueInclusion`, `algebraicResidueAut_stage_isFrobPow`). The residue field of the
stage maps into that of `U` (`LocalGalois.residueInclusion` after `stageIntegerEquiv` of
`Wintenberger.NormField` and `stageSpectralEquiv`), equivariantly by `autEquiv_of_galoisStage`, so
`FrobPowAt.map` carries the property to `x`.

`relFieldOfNorms_localResidueDegree` composes this with `residueHom_autCongr_isFrobPow` (transport
to `Ω'` along `e`) and `localResidueDegree_eq_frobenius_iff` of `Wintenberger.Degree`.

## Declarations used

From the FontaineWintenberger library: `RelFieldOfNorms`, `RelFieldOfNorms.exists_stage`,
`RelFieldOfNorms.transition`, `RelFieldOfNorms.of_transition`, `RelFieldOfNorms.of`,
`RelFieldOfNorms.autEquiv`, `RelFieldOfNorms.autEquiv_of`, `RelFieldOfNorms.stageMap_apply`,
`RelFieldOfNorms.of_transport_congr`, `FieldOfNorms.autEquiv`, `FieldOfNorms.autEquiv_apply`,
`FieldOfNorms.fieldValuation`, `FieldOfNorms.residueEquiv`, `FieldOfNorms.residueAut_residue`,
`FieldOfNorms.residueAut_residueEquiv`, `algebraicResidueAut`, `algebraicResidueAut_residue`,
`integralClosureResidueInclusion`, `integralClosureResidueInclusion_residue`,
`integralClosure_valuationRing`, `spectralIntegerRing`. From the Library: `LocalGalois.localNormedField`,
`LocalGalois.extensionIntegers`, `LocalGalois.residueHom`, `LocalGalois.residueInclusion`,
`LocalGalois.integerInclusion`, `LocalGalois.integerAut`, `Weil.Local.SepClosed.localResidueDegree`,
`Weil.Local.SepClosed.localResidueField`. From `Wintenberger`: `galoisStage`, `stageImage`,
`stageGalois`, `stageIntegerEquiv`, `relFieldOfNorms_isSepClosure`,
`localField_isPerfectResidueLocalField`, `IsFrobPow`, `FrobPowAt.map`, `FrobPowAt.of_map`,
`residueHom_autCongr_isFrobPow`, `localResidueDegree_eq_frobenius_iff`. From Mathlib:
`IntermediateField.normalClosure`, `IntermediateField.le_normalClosure`,
`AlgEquiv.restrictNormal_commutes`, `IntermediateField.normal_iff_forall_map_eq'`.

## Sources

Wintenberger 1983, Théorème 2.1.3 (ii) (the residue field of `X_K(L)` is that of `L`) and §3.1–3.2
(functoriality of the field of norms and the isomorphism `G_L ≃ G_{X_K(L)}`); Serre, *Local Fields*,
Chapter I, §7 (residue actions in a tower).
