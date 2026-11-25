/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorComparisonNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

/-! # Compatible finite coordinates for ordinary tensor pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite ordinary tensor comparisons, before assembly on the sequence site.

Source: Stacks 03EL, Zheng Construction 4.1, and blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-tensor-level-coordinates).

Proof: forget the derived fields of g.generic and apply the existing ordinary tensor
existence theorem. Its system comparisons are natural in both factors. Conjugate
by the natural isomorphisms between the explicit site tensor and the monoidal
sheaf tensor, and transport along the specified coefficient, transition and
ordinary pull-functor equalities. Evaluate this constructed natural isomorphism
to obtain delta. Naturality of the actual system transition with respect to its
components gives horizontal compatibility; evaluating its naturality gives the
second clause. The finite adjunction section formula is
TensorCoordinates.comparison_normalization for this fixed construction. Its
argument uses the ordinary tensor evaluation square, the generalized pure-tensor
formula, the underlying finite unit normalization and ordinary unit evaluation.
The transition and naturality clauses use no derived faithfulness assumption. -/
theorem exists_tensorLevelCoordinates {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (hpush : ∀ (n : ℕ)
      (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
      (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
          ((g.generic.levelPush n).obj N)).obj.obj U),
      HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x) :
    ∃ δ : ∀ (M N : Systems Y (Arings l E Y)) (n : ℕ),
      (SpTowerShriek.ev l E X n).obj (g.pull.obj ((tensorRight l E Y N).obj M)) ≅
        (SpTowerShriek.ev l E X n).obj
          ((tensorRight l E X (g.pull.obj N)).obj (g.pull.obj M)),
      (∀ (M N : Systems Y (Arings l E Y)) {m n : ℕ} (h : n ≤ m),
        (SemilinearSections.transition (Scheme.ProEt.topology X)
            (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
            (g.pull.obj ((tensorRight l E Y N).obj M)) ≫
          (SemilinearSections.res (SemilinearSections.coefficientMap
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h)).map (δ M N n).hom =
        (δ M N m).hom ≫ (SemilinearSections.transition (Scheme.ProEt.topology X)
          (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
            ((tensorRight l E X (g.pull.obj N)).obj (g.pull.obj M))) ∧
      (∀ (N : Systems Y (Arings l E Y)) {M M' : Systems Y (Arings l E Y)}
        (a : M ⟶ M') (n : ℕ),
        (SpTowerShriek.ev l E X n).map
            (g.pull.map ((tensorRight l E Y N).map a)) ≫ (δ M' N n).hom =
          (δ M N n).hom ≫ (SpTowerShriek.ev l E X n).map
            ((tensorRight l E X (g.pull.obj N)).map (g.pull.map a))) ∧
      ∀ (M N : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
        HEq
          ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
            _ _) ((g.ordinaryPullEvaluation n).inv.app ((tensorRight l E Y N).obj M) ≫
              (δ M N n).hom)).val.app U
                (tensorPure l E Y M N (op (n, U.unop)) x y))
          (tensorPure l E X (g.pull.obj M) (g.pull.obj N)
            (op (n, (chart f U).unop))
            (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
            (sectionAdjoint l E g (𝟙 (g.pull.obj N)) n U y)) := by
  classical
  have : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  obtain ⟨T⟩ := SemilinearSections.geometricOrdinaryTensor_exists.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
    (Scheme.ProEt.topology X)
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))
    (TensorCoordinates.ordinaryGeometry l E g)
  let κ := TensorCoordinates.comparison l E g T
  refine ⟨fun M N n ↦ (SpTowerShriek.ev l E X n).mapIso ((κ N).app M), ?_, ?_, ?_⟩
  · intro M N m n h
    exact ((SemilinearSections.transition (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).naturality
        ((κ N).hom.app M)).symm
  · intro N M M' a n
    simpa only [Functor.map_comp, Functor.comp_map, Functor.mapIso_hom, Iso.app_hom]
      using congrArg ((SpTowerShriek.ev l E X n).map) ((κ N).hom.naturality a)
  · intro M N n U x y
    exact TensorCoordinates.comparison_normalization l E g T hpush M N n U x y

end AlgebraicGeometry.ProEtale.SpTowerClasses
