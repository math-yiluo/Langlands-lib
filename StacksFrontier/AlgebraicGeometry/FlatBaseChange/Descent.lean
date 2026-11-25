module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import Mathlib.Algebra.Ring.MinimalAxioms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Finite type descends along fpqc coverings

[Stacks, Tag 05AZ]: a quasi-coherent `𝒪_X`-module is of finite type as soon as its pullback to
every member of an fpqc covering is. This file proves it,
`Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`.

The statement is local on the base, so it suffices to treat an affine base. There a
quasi-compact fpqc covering is refined by a finite family of affine schemes flat over the base;
their coproduct is affine, flat and surjective over the base, hence faithfully flat on global
functions; and finite generation of modules descends along a faithfully flat ring map, which is
[Stacks, Tag 03C4] and is Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`:
  **[Stacks, Tag 05AZ].** Finite type of a quasi-coherent module descends along an fpqc
  covering.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_specMap_pullback`: the affine core,
  read on a faithfully flat ring map and the associated sheaf of a module.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_flat_surjective_of_isAffine`: the
  affine case, for a flat surjective morphism of affine schemes.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_openCover`: being of finite type is
  local on an open cover of a scheme.

## Implementation notes

The shape of the argument is that of
`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`
(`StacksFrontier/AlgebraicGeometry/Descent/Modules/FpqcFinitePresentation.lean`, [Stacks, Tag
05B0]), whose affine pieces are reused here in the finite-type form. The one ingredient the
finite-presentation file does not have an analogue of is the transport of
`SheafOfModules.IsFiniteType` from `M.restrict U.ι` to `M.over U` for an open `U` of a scheme;
it is `isFiniteType_over` here, proved from the generic site statement
`isFiniteType_pushforward` along the equivalence between the slice of the opens site at `U` and
the opens site of `U`. With that, locality is `Stacks.SheafOfModules.LocalKernel`'s
`isFiniteType_of_coversTop` and no finite global generating family is needed, which is why the
finite-presentation file's affine presentation machinery has no counterpart below.

Several invertibility and finite-type hypotheses are passed as *explicit* arguments rather than
as instances (`isFiniteType_pushforward` takes `hφ` and `hM` explicitly, and each use of
`Stacks.SheafOfModules.isFiniteType_of_iso` is preceded by a `have` that restates its source in
the spelling the iso uses). The reason is that instance search compares the objects at
`instances` transparency, where `(F ⋙ G).obj M` and `G.obj (F.obj M)` do not agree; an explicit
argument is checked at default transparency instead.

## References

* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### The affine core -/

/-! ### Locality on an open cover -/

/-! ### Descent along an fpqc covering -/

/-- A quasi-compact fpqc covering of an affine scheme is refined, through open immersions, by a
finite affine covering by flat morphisms. -/
theorem exists_finite_affine_refinement
    {S : Scheme.{u}} [IsAffine S] (𝒰 : S.Cover.{v} Scheme.fpqcPrecoverage) :
    ∃ (𝒱 : Scheme.AffineCover.{v} @Flat S) (f : 𝒱.cover ⟶ 𝒰.forgetQc),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  let _ : MorphismProperty.RespectsLeft (@Flat) (@IsOpenImmersion) :=
    (inferInstance : MorphismProperty.Respects (@Flat) (@IsOpenImmersion)).toRespectsLeft
  let _ : QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp (𝒰.mem₀ : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S).1
  have : CompactSpace S := inferInstance
  exact QuasiCompactCover.exists_hom (P := @Flat) (𝒰 := 𝒰.forgetQc)

/-- The map out of the coproduct of a finite affine flat covering of an affine scheme is flat,
surjective and quasi-compact. -/
theorem affine_sigmaDesc_fpqc {S : Scheme.{u}} [IsAffine S]
    (𝒱 : Scheme.AffineCover.{v} @Flat S) [Finite 𝒱.I₀] [Small.{u} 𝒱.cover.I₀] :
    Flat (Sigma.desc 𝒱.cover.f) ∧ Surjective (Sigma.desc 𝒱.cover.f) ∧
      QuasiCompact (Sigma.desc 𝒱.cover.f) := by
  let _ : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have (j : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X j) := inferInstanceAs (IsAffine (Spec (𝒱.X j)))
  have : IsAffine (∐ 𝒱.cover.X) := inferInstance
  have (j : 𝒱.cover.I₀) : Flat (𝒱.cover.f j) := 𝒱.map_prop j
  have : Surjective (Sigma.desc 𝒱.cover.f) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := 𝒱.covers x
    refine ⟨Sigma.ι 𝒱.cover.X (𝒱.idx x) y, ?_⟩
    calc (Sigma.desc 𝒱.cover.f) (Sigma.ι 𝒱.cover.X (𝒱.idx x) y)
        = (Sigma.ι 𝒱.cover.X (𝒱.idx x) ≫ Sigma.desc 𝒱.cover.f) y := rfl
      _ = (𝒱.cover.f (𝒱.idx x)) y :=
          congrArg (fun q : 𝒱.cover.X (𝒱.idx x) ⟶ S => q y)
            (Sigma.ι_comp_desc 𝒱.cover.f (𝒱.idx x))
      _ = x := hy
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Stacks.AlgebraicGeometry.FlatBaseChange

end
