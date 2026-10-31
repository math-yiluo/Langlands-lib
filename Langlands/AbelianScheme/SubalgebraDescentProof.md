# Proof: abelian-scheme descent from scheme, group-law and property descent

`Langlands.AbelianScheme.subalgebraDescentReduction` proves
`Langlands.AbelianScheme.SubalgebraDescentReductionStatement.{u}`. See
`SubalgebraDescentReductionStatement.md` for the statement. The work is done by
`Langlands.AbelianScheme.SubalgebraDescentProof.subalgebraDescent_of`, which takes the six
hypotheses as arguments. `Langlands.AbelianScheme.subalgebraDescent` applies the reduction to the
six hypotheses proved in the Library (see *Unconditional form*).

## Stages

Fix `R : CommRingCat.{u}` and `A : AbelianScheme (Spec R)`. A `Stage A` consists of:
- a subalgebra `R₀ : Subalgebra ℤ R` with `R₀.FG`;
- a group scheme `G` over `Spec (CommRingCat.of ↥R₀)` with `IsCommMonObj G.X`;
- an isomorphism of group schemes
  `e : A.toGrp ≅ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))).obj G`.

`Stage.step M T hT` enlarges a stage along a finitely generated `↥M.R₀`-subalgebra `T` of `R`.
The new ring is `T.restrictScalars ℤ`, finitely generated over `ℤ` by `fg_restrictScalars`
(transitivity of finite type). The new group scheme is the base change of `M.G` along
`Spec T ⟶ Spec R₀`; it stays commutative by `Functor.isCommMonObj_obj`. The new isomorphism is
`M.e`, followed by the identification of pullbacks along equal maps (`specMap_comp`:
`Spec.map (R₀ → R)` is `Spec.map (T → R) ≫ Spec.map (R₀ → T)`), followed by the Library's
composition comparison `GroupScheme.baseChangeCompIso`. By definition, the underlying morphism of
the new group scheme is `pullback.snd M.G.X.hom (Spec.map (R₀ → T))` (`Stage.step_hom`). This is
exactly the morphism whose properties the five descent hypotheses conclude.

Properties of morphisms are moved with base change in two ways. `prop_snd` applies
`MorphismProperty.of_isPullback` to the chosen pullback square. `prop_of_iso` transfers a
property along an isomorphism of group schemes, using the pullback square
`IsPullback.of_horiz_isIso` over `𝟙`. Both need only `IsStableUnderBaseChange`, which Mathlib
provides for every property used here. `Stage.prop_baseChange` combines `prop_of_iso` with `M.e`.
It gives each property of `A.X.hom` for the base change of `M.G.X.hom` to `Spec R`. Finitely
generated subrings are noetherian (`isNoetherianRing_of_fg`, via
`Algebra.FiniteType.isNoetherianRing`).

## The first stage

`exists_stage₀` applies the scheme-descent hypothesis to `A.X.hom`, with `A₀` the prime subring
`↥(⊥ : Subalgebra ℤ R)`. The structure morphism is quasi-compact, quasi-separated and locally of
finite presentation because `A` is proper and smooth. This gives `T₀`, `f₀ : X₀ ⟶ Spec T₀` and a
pullback square. The group-law hypothesis, applied with `A₀ := ↥T₀`, then gives `T₁`, a group
scheme `G₀` over `Spec T₁` whose underlying morphism is a base change of `f₀`, its
commutativity, and the isomorphism `A.toGrp ≅` base change of `G₀`. The ring is
`T₁.restrictScalars ℤ`, finitely generated over `ℤ` by `fg_restrictScalars_bot` (the tower
`ℤ → ⊥ → T₀ → T₁`). Quasi-compactness, quasi-separatedness and local finite presentation of
`G₀.X.hom` follow from those of `f₀` by `MorphismProperty.of_isPullback`.

## Assembly

`subalgebraDescent_of` runs four further stages with the empty finite set:
1. separatedness descent at the first stage (`G₀.X.hom` is quasi-compact and quasi-separated);
2. properness descent at the next stage: its ring is noetherian, and its morphism is separated,
   quasi-compact and of finite type;
3. smoothness descent: the morphism is proper (so quasi-compact) and locally of finite
   presentation;
4. geometric-connectedness descent: the ring is noetherian and the morphism is proper and smooth.

At each step the hypothesis needs the property for the base change to `Spec R`, which
`Stage.prop_baseChange` provides. The properties already obtained carry over to the next stage
by `prop_snd`. The last stage `M₄` has a commutative group scheme whose structure morphism is
smooth, proper and geometrically connected. These are the fields of an abelian scheme `A₀` over
`Spec (CommRingCat.of ↥M₄.R₀)`. The isomorphism `A ≅ (AbelianScheme.baseChange _).obj A₀` is
`M₄.e`, wrapped in `Additive.ofMul` as morphisms of abelian schemes require.

## Unconditional form

`Langlands.AbelianScheme.subalgebraDescent` proves
`Langlands.AbelianScheme.SubalgebraDescentStatement.{u}`: every abelian scheme over `Spec R` is
isomorphic to the base change of an abelian scheme over `Spec R₀`, for a finitely generated
subring `R₀` of `R`. It applies `subalgebraDescentReduction` to the six proofs of the
hypotheses in the Library:
- `Langlands.AlgebraicGeometry.NoetherianApproximation.schemeSubalgebraDescent`
  (module `Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof`);
- `Langlands.GroupScheme.subalgebraDescent`
  (module `Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof`);
- `Langlands.AlgebraicGeometry.NoetherianApproximation.isSeparatedSubalgebraDescent`
  (module `Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof`);
- `Langlands.AlgebraicGeometry.NoetherianApproximation.isProperSubalgebraDescent`
  (module `Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof`);
- `Langlands.AlgebraicGeometry.NoetherianApproximation.smoothSubalgebraDescent`
  (module `Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof`);
- `Langlands.AlgebraicGeometry.NoetherianApproximation.geometricallyConnectedSubalgebraDescent`
  (module `Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof`).

## Provenance

Internal. The order of the stages follows the assembly in the Anthropic FLT Lean source
`P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean`
at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (namespace `NoethModel17`). This proof is
written for the Library's `Grp (Over S)`; see the licence section for the parts adapted from
that file.

## Licence and attribution

The helper lemmas `fg_restrictScalars`, `isNoetherianRing_of_fg` and `specMap_comp`, and the order of the stages, are adapted from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean`,
namespace `NoethModel17`. That work is Copyright 2026 Anthropic, PBC, and is licensed under the
Apache License, Version 2.0. The Lean file carries a notice recording the adaptation. Unmodified
copies of the source's `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in the Library as
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for that source file, so no third-party
notice is recorded for it; the limits stated in its section 5 apply.
