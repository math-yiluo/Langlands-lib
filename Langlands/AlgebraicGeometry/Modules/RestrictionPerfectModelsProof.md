# Restriction-compatible perfect models: proof

Module `Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsProof`
proves `RestrictionPerfectModelsStatement.{u}`. It shows that every line bundle
on a smooth proper family over an affine base has a universal perfect model
(`UniversalPerfectModel`, defined in `RestrictionPerfectModelsReduction`), then
applies the reduction `restrictionPerfectModels_of_universalPerfectModel`. The
module locally selects Mathlib's `HasDerivedCategory.standard`.

Notation as in `RestrictionPerfectModelsReduction.md`: `Q = DerivedCategory.Q`,
`RΓ_R(X, M)` for actual derived relative global sections, and `K ⊗ T` for
termwise scalar extension `(ModuleComplex.baseChange φ.hom).obj K`.

## `universalPerfectModel`

For `R : CommRingCat.{u}`, `X : Scheme.{u}`, `f : X ⟶ Spec R` with instances
`[Smooth f] [IsProper f]`, and `L : Picard.LineBundle X`:
`UniversalPerfectModel f L`.

Proof.

1. The published theorem `universalPerfectSections` gives a strictly perfect
   complex `K` of `R`-modules and some derived isomorphism
   `e : Q.obj K ≅ RΓ_R(X, L.obj)`. Its base-change part is not used.
2. `X` is quasi-compact because `f` is quasi-compact and `Spec R` is compact.
   Let `𝒰 = Scheme.OrderedAffineCover.ofCompactSpace X`, a finite ordered
   affine open cover. Let `C` be the alternating Čech complex
   `(CechResolution.cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat`,
   indexed by `ℤ` and zero in negative degrees. `f` is separated (it is
   proper) and `L.obj` is quasi-coherent, so the published canonical
   comparison `c = CechResolution.cechDerivedComparison f 𝒰 L.obj :
   Q.obj C ⟶ RΓ_R(X, L.obj)` is an isomorphism (`cechDerivedComparisonIso`).
3. By `exists_chainMap_of_isStrictlyPerfect`, the derived morphism `e ≫ c⁻¹` is
   `Q.map v` for a chain map `v : K ⟶ C`. Then `Q.map v ≫ c = e`.
4. The model is `K` with `a = Q.map v ≫ c`. It is an isomorphism because it
   equals `e`.
5. Universality. Fix a pullback square
   `hp : IsPullback p f' f (Spec.map φ)` with `φ : R ⟶ T`. The published
   criterion `CechResolution.isIso_perfectModelBaseChange_cechDerivedComparison_iff hp L 𝒰 v hK`
   says that `perfectModelBaseChange hp L hK (Q.map v ≫ c)` is an isomorphism
   if and only if the termwise scalar extension
   `(ModuleComplex.baseChange φ.hom).map v` is a quasi-isomorphism. That
   criterion holds for an arbitrary ring map `φ`; it identifies the base change
   of `a` with the scalar extension of `v` followed by the Čech comparison on
   `X'`, which is invertible.
6. `v` is a quasi-isomorphism, because `Q.map v = e ≫ c⁻¹` is an isomorphism
   (`DerivedCategory.isIso_Q_map_iff_quasiIso`).
7. Both `K` and `C` vanish strictly above `max b n`, where `K` vanishes
   strictly above `b` (part of `IsStrictlyPerfect`) and `n` is the number of
   cover members (`CechResolution.isStrictlyLE_extend_cechCochainComplex`).
   The terms of `K` are projective, hence flat. The terms of `C` are flat
   `R`-modules by `CechResolution.flat_extend_cechCochainComplex_X`, which uses
   that `f` is flat (it is smooth) and separated and that `L` is locally
   trivial.
8. The theorem `ModuleComplex.quasiIso_baseChange_map_of_flat`
   (scalar extension along any ring map preserves quasi-isomorphisms between
   bounded-above complexes of flat modules) now shows that
   `(ModuleComplex.baseChange φ.hom).map v` is a quasi-isomorphism. By step 5,
   the base change of `a` is an isomorphism.

## `restrictionPerfectModels`

`restrictionPerfectModels : RestrictionPerfectModelsStatement.{u}` is
`restrictionPerfectModels_of_universalPerfectModel` applied to
`universalPerfectModel`. The hypotheses `Smooth f` and `IsProper f` are turned
into instances for this application.

## Dependencies

Library results used:

- `universalPerfectSections`, `Scheme.OrderedAffineCover.ofCompactSpace`,
  `CechResolution.cechDerivedComparison` and `cechDerivedComparisonIso`,
  `DerivedSections.perfectModelBaseChange`.
- `Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange`
  (`quasiIso_baseChange_map_of_flat`).
- `Langlands.AlgebraicGeometry.Modules.CechResolution.ScalarCochainBaseChange`
  (boundedness and flatness of the Čech terms) and
  `Langlands.AlgebraicGeometry.Modules.CechResolution.PerfectModelBaseChange`
  (the base-change criterion).
- The proposition `RestrictionPerfectModelsStatement` from
  `Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement`,
  imported through `RestrictionPerfectModelsReduction`.

## Provenance

Internal. This is the standard argument that cohomology and base change for a
flat proper family can be computed from one finite complex: Stacks Project
Lemma 0A1H/0B91 and Remark 0A1I (`perfect.tex`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, lines 7395–7544), as recorded in
`RestrictionPerfectModelsStatement.md`. The Lean route differs from the
source's general derived-category argument. It uses the Čech complex of a
finite affine cover as a flat bounded representative, a chain-level lift from
a strictly perfect model, and flat scalar extension of quasi-isomorphisms. No
noetherian hypothesis is used.
