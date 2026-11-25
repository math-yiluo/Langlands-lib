/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorComparison

/-! # Coordinates for finite tensor adjunctions

Source: Stacks 03EL; Zheng Construction 4.1; blueprint tower-operations proof (2).
(blueprint: lem-sfb-tensor-comparison-coordinate-conjugation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r u
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
attribute [local irreducible] Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDirectImageMap Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction CategoryTheory.constantSheaf
  Padic Padic.coefficientExtensionIntegers SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
attribute [local implicit_reducible] spCoefficientCommRings SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev siteRight {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r}) (N : SemilinearSections.Mod.{c, v, max c v r} J R) :=
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  SheafOfModules.siteSheafTensorRight (A := R) N

private abbrev sitePair {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r}) (M N : SemilinearSections.Mod.{c, v, max c v r} J R)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :=
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  SheafOfModules.siteSheafTensorTmul M N U x y

/-- The constructed comparison is conjugation by the two explicit site tensor bridges.
Source: Stacks 03EL; blueprint tower-operations proof, clause (2).
(blueprint: lem-sfb-tensor-comparison-coordinate-conjugation).

Proof: eliminate the coefficient, transition and pull-functor equalities. The construction
of comparisonOfCoordinates is then this composite, by definition. -/
theorem tensorComparison_coordinates {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ n, B' (n + 1) ⟶ B' n)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (F : SpTowerShriek.S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ') (hF : HEq g.pull F)
    (μ : ∀ N : SpTowerShriek.S l E Y,
      let := SheafOfModules.isMonoidal_W_independentCoefficients
        (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
          (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
      let := SheafOfModules.monoidalCategory
        (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
          (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
      let := SheafOfModules.isMonoidal_W_independentCoefficients
        (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ')
      let := SheafOfModules.monoidalCategory
        (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ')
      CategoryTheory.MonoidalCategory.tensorRight N ⋙ F ≅
        F ⋙ CategoryTheory.MonoidalCategory.tensorRight (F.obj N))
    (M N : Systems Y (Arings l E Y)) :
    HEq ((comparisonOfCoordinates l E g B' τ' hB hτ F hF μ N).hom.app M)
      (F.map ((siteTensorIso.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (systemRing l E Y) N).hom.app
            M) ≫ (μ N).hom.app M ≫
        (siteTensorIso.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ')
          (F.obj N)).inv.app (F.obj M)) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  rfl

private theorem transport_pure {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (F : SpTowerShriek.S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ') (hF : HEq g.pull F)
    (k : ∀ M N : Systems Y (Arings l E Y),
      g.pull.obj ((tensorRight l E Y N).obj M) ⟶
        (tensorRight l E X (g.pull.obj N)).obj (g.pull.obj M))
    (d : ∀ M N : Systems Y (Arings l E Y),
      F.obj ((tensorRight l E Y N).obj M) ⟶
        (siteRight.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ') (F.obj N)).obj
            (F.obj M))
    (hk : ∀ M N, HEq (k M N) (d M N)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : ∀ (M : Systems Y (Arings l E Y)) (_x : M.val.obj (op (n, U.unop))),
      (F.obj M).val.obj (op (n, (chart f U).unop)))
    (hs : ∀ M x, HEq (s M x) (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x))
    (hp : ∀ (M N : Systems Y (Arings l E Y))
      (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
      (d M N).val.app (op (n, (chart f U).unop))
        (s _ (tensorPure l E Y M N (op (n, U.unop)) x y)) =
        sitePair.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ') (F.obj M) (F.obj N)
          (op (n, (chart f U).unop)) (s M x) (s N y))
    (M N : Systems Y (Arings l E Y))
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (k M N).val.app (op (n, (chart f U).unop))
      (sectionAdjoint l E g (𝟙 (g.pull.obj ((tensorRight l E Y N).obj M))) n U
        (tensorPure l E Y M N (op (n, U.unop)) x y)) =
      tensorPure l E X (g.pull.obj M) (g.pull.obj N) (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
        (sectionAdjoint l E g (𝟙 (g.pull.obj N)) n U y) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  have hx := eq_of_heq (hs M x)
  have hy := eq_of_heq (hs N y)
  have hz := eq_of_heq (hs _ (tensorPure l E Y M N (op (n, U.unop)) x y))
  have h := hp M N x y
  rw [hz, hx, hy] at h
  simpa only [← eq_of_heq (hk M N), sitePair, siteRight,
    tensorPure, tensorRight] using h

end AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
