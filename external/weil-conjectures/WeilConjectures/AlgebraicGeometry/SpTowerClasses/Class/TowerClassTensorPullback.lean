/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTwisting
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjoint

/-! # Ordinary tensor pullback with its adjoint section normalization -/

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

/-- The actual ordinary tensor functor with a fixed second factor on the coefficient site.
Source: Stacks 03EK; the tensor in classes (4).
(blueprint: def-sfb-tower-class-tensor-pullback). -/
def tensorRight (T : Scheme.{u}) (N : Systems T (Arings l E T)) :
    Systems T (Arings l E T) ⥤ Systems T (Arings l E T) :=
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  SheafOfModules.siteSheafTensorRight (A := systemRing l E T) N

/-- The sheafification-unit pure tensor for the same ordinary tensor functor.
Source: Stacks 03EK; classes (4).
(blueprint: def-sfb-tower-class-tensor-pullback). -/
def tensorPure (T : Scheme.{u}) (M N : Systems T (Arings l E T))
    (U : (ℕ × T.ProEt)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((tensorRight l E T N).obj M).val.obj U :=
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  SheafOfModules.siteSheafTensorTmul M N U x y

/-- Ordinary inverse image preserves tensor products, before any localization.
The comparison is normalized by the actual system adjunction on each finite chart.
Source: blueprint tower-operations proof (2), tensor and adjunction recipe; Stacks 03EL.
(blueprint: def-sfb-tower-class-tensor-pullback). -/
structure TensorPullback {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : SpTowerShriek.Geometry l E b f) where
  iso : ∀ N : Systems Y (Arings l E Y),
    tensorRight l E Y N ⋙ g.pull ≅ g.pull ⋙ tensorRight l E X (g.pull.obj N)
  normalization : ∀ (M N : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
    HEq (sectionAdjoint l E g ((iso N).hom.app M) n U
      (tensorPure l E Y M N (op (n, U.unop)) x y))
      (tensorPure l E X (g.pull.obj M) (g.pull.obj N)
        (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
        (sectionAdjoint l E g (𝟙 (g.pull.obj N)) n U y))

end AlgebraicGeometry.ProEtale.SpTowerClasses
