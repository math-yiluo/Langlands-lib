# The filtration of the field of norms and the Library's filtration of a local field

Module `Langlands.LocalFactor.Ramification.Wintenberger.NormField`, namespace
`Langlands.Ramification.Wintenberger`.

Let `K` be a field of `FontaineWintenberger.IsPerfectResidueLocalField`, `L/K` an infinite
separable arithmetically profinite extension, and `Ω` a separable closure of `K` and of `L`. The
FontaineWintenberger library constructs the field of norms `X = FieldOfNorms K L`, the relative
field of norms `U = RelFieldOfNorms K L Ω` (the union of the norm fields `X_K(N)` of the finite
extensions `N` of `L` in `Ω`, a separable closure of `X`), the isomorphism
`RelFieldOfNorms.autEquiv : Gal(Ω/L) ≃* Gal(U/X)` (Wintenberger, Corollaire 3.2.3), and an upper
filtration `RelFieldOfNorms.normUpperRamificationGroup K L Ω v` of `Gal(U/X)`, whose finite levels
are the upper groups of `Gal(N/L)` acting on the valuation ring of `X_K(N)`. This file identifies
that filtration with the Library's filtration `Local.localAbsoluteUpperRamificationGroup` of a
Mathlib local field `X'` that is identified with `X`.

## Hypotheses

`X'` is a Mathlib nonarchimedean local field (`[ValuativeRel X'] [TopologicalSpace X']
[IsNonarchimedeanLocalField X']`) with algebra structures `X' → X → U` forming a scalar tower,
such that `algebraMap X' X` is bijective (`hbij`) and identifies the valuative relation of `X'`
with the valuation of the field of norms (`hval : ∀ x y : X', x ≤ᵥ y ↔ v_X(x) ≤ v_X(y)`, with
`v_X = FontaineWintenberger.FieldOfNorms.fieldValuation K L`). On `X'` the Library's normed-field
adapter `LocalGalois.localNormedField X'` is installed locally.

## Main statements

- `relFieldOfNorms_isSepClosure (hbij) : IsSepClosure X' (RelFieldOfNorms K L Ω)`.
- `restrictScalarsMulEquiv R S A (h : Function.Surjective (algebraMap R S)) :
  (A ≃ₐ[S] A) ≃* (A ≃ₐ[R] A)`; `isGalois_of_surjective`, `finiteDimensional_of_surjective`: a
  finite Galois extension of `F` is finite Galois over any field mapping onto `F`.
- For a finite Galois subextension `N` of `Ω/L`: `galoisStage L Ω N`, its image
  `stageImage K L Ω N = RelFieldOfNorms.finiteImage K L Ω (galoisStage L Ω N)` in `U`, the
  isomorphism `stageEquiv K L Ω N : FieldOfNorms K N ≃ₐ[X] stageImage K L Ω N`, the image as a
  finite Galois subextension over `X'`, `stageGalois K L Ω X' hbij N`, and `stageRingEquiv`.
- `stageValuation` (the valuation of `X_K(N)` on the stage over `X'`) and
  `stageValuation_hasExtension (hval) (N)`: it extends the norm valuation of `X'`.
- `spectralIntegerRing_stage_eq (N) : FontaineWintenberger.spectralIntegerRing X'
  (stageGalois K L Ω X' hbij N) = (stageValuation K L Ω X' hbij N).valuationSubring`, and the ring
  isomorphism `stageIntegerEquiv` from the valuation ring of `X_K(N)` to these spectral integers.
- `stageAutEquiv (N) : ((galoisStage L Ω N).val ≃ₐ[L] (galoisStage L Ω N).val) ≃*
  (stageGalois K L Ω X' hbij N ≃ₐ[X'] stageGalois K L Ω X' hbij N)`, the composite of
  `FieldOfNorms.autEquiv`, conjugation by `stageEquiv` and restriction of scalars to `X'`;
  `stageIntegerEquiv_smul`: `stageIntegerEquiv` is equivariant for it.
- `stage_upperRamificationGroup_map (N) (hv : -1 ≤ v) :
  (FieldOfNorms.upperRamificationGroup K L (galoisStage L Ω N).val v).map
  (stageAutEquiv K L Ω X' hbij N).toMonoidHom = FontaineWintenberger.upperRamificationGroup
  (R := FontaineWintenberger.spectralIntegerRing X' (stageGalois K L Ω X' hbij N)) _ v`.
- `stageAutEquiv_restrictNormal (N) (τ : Ω ≃ₐ[L] Ω) : stageAutEquiv K L Ω X' hbij N
  (τ.restrictNormal (galoisStage L Ω N).val) = ((RelFieldOfNorms.autEquiv K L Ω τ).restrictScalars
  X').restrictNormal (stageGalois K L Ω X' hbij N)`.
- `stageGalois_cofinal (D) : ∃ N, D ≤ stageGalois K L Ω X' hbij N`.
- `mem_normUpperRamificationGroup_iff (σ : U ≃ₐ[X] U) (hv : -1 ≤ v) :
  σ ∈ RelFieldOfNorms.normUpperRamificationGroup K L Ω v ↔ σ.restrictScalars X' ∈
  Local.localAbsoluteUpperRamificationGroup X' U v`.

## Proofs

The stage valuation extends the norm valuation of `X'`: on `X'` it is the valuation of `X_K(N)` on
the image of `X`, which extends that of `X` (`FieldOfNorms.fieldValuation_hasExtension_inclusion`),
which is `hval`. A valuation extending the norm of a complete discretely valued field to a finite
separable extension has the spectral integers as valuation ring
(`spectralIntegerRing_eq_extension_valuationSubring`); this identifies the two integer rings. The
action of `Gal(N/L)` on the valuation ring of `X_K(N)` is through `FieldOfNorms.autEquiv`
(`FieldOfNorms.coe_integerGaloisAction_smul`), so `stageIntegerEquiv` is equivariant, and the
FontaineWintenberger transport lemma `upperRamificationGroup_map_equivariant` identifies the upper
groups. On a stage, `RelFieldOfNorms.autEquiv τ` acts as the norm-field automorphism of
`τ|N` (`RelFieldOfNorms.autEquiv_of`, `RelFieldOfNorms.of_transport_congr`, using `τ(N) = N`).

The Library's filtration of `X'` in `U` is the FontaineWintenberger infinite filtration
(`Absolute.upperRamificationGroupInfinite_eq_local`), which may be tested on any cofinal family of
finite Galois subextensions (`mem_upperRamificationGroupInfinite_iff_cofinal`). The stages are
cofinal: every finite subextension of `U` lies in the image of a finite norm field
(`RelFieldOfNorms.exists_finiteImage_ge`), and the image of the Galois closure contains it
(`RelFieldOfNorms.finiteImage_le_iff`). The filtration of the field of norms is, by definition,
tested on the same stages (`RelFieldOfNorms.mem_upperRamificationGroup`).

## Declarations used

From the FontaineWintenberger library: `FieldOfNorms`, `FieldOfNorms.fieldValuation`,
`FieldOfNorms.inclusion`, `FieldOfNorms.autEquiv`, `FieldOfNorms.autEquiv_apply`,
`FieldOfNorms.isGalois`, `FieldOfNorms.integerGaloisAction`, `FieldOfNorms.upperRamificationGroup`,
`FieldOfNorms.fieldValuation_hasExtension_inclusion`, `RelFieldOfNorms`, `RelFieldOfNorms.of`,
`RelFieldOfNorms.ofAlgHom`, `RelFieldOfNorms.finiteImage`, `RelFieldOfNorms.finiteImage_finite`,
`RelFieldOfNorms.finiteImage_le_iff`, `RelFieldOfNorms.exists_finiteImage_ge`,
`RelFieldOfNorms.isSeparable`, `RelFieldOfNorms.isSepClosed`, `RelFieldOfNorms.autEquiv`,
`RelFieldOfNorms.autEquiv_of`, `RelFieldOfNorms.stageMap_apply`,
`RelFieldOfNorms.of_transport_congr`, `RelFieldOfNorms.upperRamificationGroup`,
`RelFieldOfNorms.mem_upperRamificationGroup`, `RelFieldOfNorms.normUpperRamificationGroup`,
`RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_iff`, `spectralIntegerRing`,
`spectralIntegerRing_eq_extension_valuationSubring`, `upperRamificationGroup_map_equivariant`,
`mem_upperRamificationGroupInfinite_iff_cofinal`. From the Library:
`Local.localAbsoluteUpperRamificationGroup`, `LocalGalois.localNormedField`,
`LocalGalois.localNormedField_le`.

## Sources

Wintenberger 1983, §3.2 (extensions of `L` and of `X_K(L)`, Corollaire 3.2.3) and §3.3
(propriétés de ramification: the ramification of `X_{L/K}(M)/X_K(L)` is computed on the finite
layers, Corollaire 3.3.6). Serre, *Local Fields*, Chapter II, §2 (uniqueness of the extension of a
complete discrete valuation) and Chapter IV, §3 (upper numbering of an infinite Galois extension,
tested on the finite quotients).
