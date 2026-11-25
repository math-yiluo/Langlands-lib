module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Descent of finitely presented modules through a limit of affine schemes

Let `D` be a cofiltered diagram of schemes with affine transition morphisms, one of whose
stages is affine, and let `S = lim D` be its limit.  This file proves that every sheaf of
`𝒪_S`-modules of finite presentation is the pullback of a sheaf of finite presentation at some
stage of the diagram.  This is the affine case of [Stacks Project, Tag 01ZR] (1), from which
the general quasi-compact quasi-separated statement is obtained in the source by Zariski
glueing.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_isLimit`:
  for a cofiltered diagram `D` of affine schemes with limit cone `c`, every
  `F : c.pt.Modules` of finite presentation is isomorphic to the pullback along `c.π.app i`
  of some `Fᵢ : (D.obj i).Modules` of finite presentation.
* `..._pullback_iso_of_isLimit_of_isAffine_stage`, in the same namespace: the same conclusion
  when only the transition morphisms are affine and a single stage is affine.

## Implementation notes

The hypotheses of the source — affine transition morphisms and quasi-compact, quasi-separated
stages — are all implied by the stages being affine, so the first statement omits them; the
second assumes only what it needs, and in particular never needs quasi-compactness or
quasi-separatedness.  It is deduced from the first by restricting the diagram to `Over i₀`,
whose forgetful functor to a cofiltered category is initial, so the whiskered cone is still a
limit, and every stage above `i₀` is affine because an affine morphism to an affine scheme has
affine source.

Three inputs are combined in the first statement.  The ring-level comparison is Mathlib's
`AlgebraicGeometry.preservesLimit_rightOp_Γ`: global sections turn a limit of affine schemes
into a colimit of rings, so `Γ(S, ⊤)` is the filtered colimit of the `Γ(D.obj i, ⊤)`.  The
module-level descent over that colimit is
`Stacks.ModuleDescent.exists_extendScalars_iso_of_isColimit`.  The passage between modules and
quasi-coherent sheaves is `AlgebraicGeometry.tilde_isFinitePresentation_iff` in one direction
and `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` — the identification of
`(Spec.map φ)^* (M^~)` with `(T ⊗_R M)^~` — for the compatibility with pullback.

The index category is left with arbitrary object and morphism universes, unrelated to the
universe `u` of the schemes.  That is possible here, where Mathlib's `AffineTransitionLimit`
API is stated only for `I : Type u` with `Category.{u} I`, because every input used is
universe-polymorphic in the shape: `preservesLimit_rightOp_Γ` is, and the joint surjectivity
of a filtered colimit of rings is proved in `StacksFrontier.AlgebraicGeometry.ModuleLimits.Algebra`
through the universal property, which needs no smallness.  The generality is not idle — the second
statement applies the first to the index category `Over i₀`, whose object universe is
`max u v`.  The quasi-compact quasi-separated case cannot currently be done this way: it rests
on `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`, whose proof goes through
`PreservesColimit D.op (forget CommRingCat)` and so through
`HasColimitsOfShape I CommRingCat.{u}`, which Mathlib provides only for `I : Type u` with
`Category.{u} I`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

/-- Pullback of a sheaf of modules of finite presentation along a morphism of schemes is of
finite presentation.  This is [Stacks Project, Tag 01BQ] transported from ringed spaces to
schemes. -/
theorem isFinitePresentation_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  let g : X.toRingedSpace ⟶ Y.toRingedSpace := f.toLRSHom.toShHom
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ g M ‹M.IsFinitePresentation›

end Stacks.AlgebraicGeometry.ModuleLimits

end
