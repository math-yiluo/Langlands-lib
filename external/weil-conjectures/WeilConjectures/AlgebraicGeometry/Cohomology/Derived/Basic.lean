/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The derived category of `𝒪_X`-modules and perfect complexes

For a scheme `X`, the category `X.Modules` of `𝒪_X`-modules is a Grothendieck abelian category
(`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`), made an instance here. Hence it has
K-injective resolutions and a derived category `D(𝒪_X) = DerivedCategory X.Modules`
(`HasDerivedCategory.ofIsGrothendieckAbelian`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.derivedPushforward f`: the derived direct image
  `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)`, the total right derived functor of the pushforward, computed on
  K-injective complexes.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteProjective`: an `𝒪_X`-module which is a direct
  summand of a free module of finite rank. On an affine scheme `Spec A` these are the modules
  `M~` with `M` a finitely generated projective `A`-module.
- `AlgebraicGeometry.Scheme.Modules.IsPerfectComplex E`: an object `E` of `D(𝒪_X)` is perfect if
  every point has an affine open neighbourhood `U` on which `E|_U` is isomorphic to a bounded
  complex of finite projective `𝒪_U`-modules.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isPerfectComplex_singleFunctor_obj_of_isInvertible`: an
  invertible module placed in degree `0` is perfect.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- `X.Modules` is a Grothendieck abelian category. As a consequence it has K-injective
resolutions and a derived category `D(𝒪_X) = DerivedCategory X.Modules`, whose objects are the
cochain complexes of `𝒪_X`-modules and whose morphisms are obtained by inverting the
quasi-isomorphisms (`HasDerivedCategory.ofIsGrothendieckAbelian`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  SheafOfModules.isGrothendieckAbelian X.ringCatSheaf

/-- The **derived direct image** `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)` along a morphism of schemes
`f : X ⟶ S`: the total right derived functor of the pushforward
`AlgebraicGeometry.Scheme.Modules.pushforward f`, computed on K-injective resolutions.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
noncomputable def derivedPushforward (f : X ⟶ Y) :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  (pushforward f).rightDerivedFunctor

/-- An `𝒪_X`-module is **finite projective** if it is a direct summand of a free module of finite
rank, that is a retract of `𝒪_X^r` for some `r`. On an affine scheme `Spec A` these are the
modules `M~` associated with the finitely generated projective `A`-modules `M`, the direct
summands of the `A^r`. -/
def IsFiniteProjective (M : X.Modules) : Prop :=
  ∃ r : ℕ, Nonempty (Retract M (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))))

lemma IsFiniteProjective.of_iso {M N : X.Modules} (h : M.IsFiniteProjective) (e : N ≅ M) :
    N.IsFiniteProjective := by
  obtain ⟨r, ⟨ρ⟩⟩ := h
  exact ⟨r, ⟨{ i := e.hom ≫ ρ.i, r := ρ.r ≫ e.inv, retract := by simp }⟩⟩

lemma IsFiniteProjective.of_isZero {M : X.Modules} (h : IsZero M) : M.IsFiniteProjective :=
  ⟨0, ⟨{ i := 0, r := 0, retract := h.eq_of_src _ _ }⟩⟩

lemma isFiniteProjective_unit : IsFiniteProjective (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨1, ⟨⟨(SheafOfModules.freeUniqueIso (ULift.{u} (Fin 1))).inv,
        (SheafOfModules.freeUniqueIso (ULift.{u} (Fin 1))).hom, by simp⟩⟩⟩

/-- An object `E` of the derived category `D(𝒪_X)` is **perfect** if it is locally, on an affine
open cover of `X`, isomorphic to a bounded complex of finite projective modules: every point `x`
has an affine open neighbourhood `U` such that the restriction `E|_U` is isomorphic in `D(𝒪_U)` to
the image of a complex `P` of `𝒪_U`-modules concentrated in some interval `[a, b]` whose terms
are finite projective (`AlgebraicGeometry.Scheme.Modules.IsFiniteProjective`). The perfect
objects form the subcategory `D_perf(𝒪_X)`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
def IsPerfectComplex (E : DerivedCategory X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (P : CochainComplex U.toScheme.Modules ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n, (P.X n).IsFiniteProjective) ∧
      Nonempty ((restrictFunctor U.ι).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)

lemma IsPerfectComplex.of_iso {E F : DerivedCategory X.Modules} (h : IsPerfectComplex E)
    (e : E ≅ F) : IsPerfectComplex F := by
  intro x
  obtain ⟨U, hU, hx, P, a, b, ha, hb, hP, ⟨e'⟩⟩ := h x
  exact ⟨U, hU, hx, P, a, b, ha, hb, hP,
    ⟨((restrictFunctor U.ι).mapDerivedCategory.mapIso e).symm ≪≫ e'⟩⟩

/-- Restriction of an invertible module to an affine open neighbourhood on which it is trivial. -/
lemma IsInvertible.exists_isAffineOpen_restrict_iso (M : X.Modules) [M.IsInvertible] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((restrictFunctor U.ι).obj M ≅ SheafOfModules.unit _) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
  obtain ⟨U, hU, hxU, hUV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxV
  change X.Opens at U
  let i : U.toScheme ⟶ V.toScheme := X.homOfLE hUV
  refine ⟨U, hU, hxU, ⟨(restrictFunctorIsoPullback U.ι).app M ≪≫
    (Modules.pullbackCongr (X.homOfLE_ι hUV).symm).app M ≪≫
    (Modules.pullbackComp i V.ι).symm.app M ≪≫ (Modules.pullback i).mapIso e ≪≫
    pullbackObjUnitIso i⟩⟩

/-- **An invertible module is perfect.** An invertible `𝒪_X`-module `ℒ`, placed in degree `0`, is
a perfect object of `D(𝒪_X)`: on an affine open `U` on which `ℒ|_U ≅ 𝒪_U`, it is the complex
`𝒪_U[0]`, whose only term is free of rank one.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem isPerfectComplex_singleFunctor_obj_of_isInvertible (M : X.Modules) [M.IsInvertible] :
    IsPerfectComplex ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  intro x
  obtain ⟨U, hU, hx, ⟨e⟩⟩ := IsInvertible.exists_isAffineOpen_restrict_iso M x
  let P := (HomologicalComplex.single U.toScheme.Modules (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit _)
  refine ⟨U, hU, hx, P, 0, 0, inferInstance, inferInstance, fun n ↦ ?_, ⟨?_⟩⟩
  · by_cases hn : n = 0
    · subst hn
      exact isFiniteProjective_unit.of_iso (HomologicalComplex.singleObjXSelf _ _ _)
    · exact IsFiniteProjective.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  · exact ((restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

end AlgebraicGeometry.Scheme.Modules
