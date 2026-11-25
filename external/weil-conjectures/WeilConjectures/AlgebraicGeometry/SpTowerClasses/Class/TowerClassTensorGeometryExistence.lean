/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassUnitLevelCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorLevelCoordinates
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation

/-! # Normalized unit and ordinary tensor coordinates for geometric tower pullback -/

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

private theorem adjoint_evaluation {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) :
    (SpTowerShriek.ev l E Y n).map ((g.ordinaryAdjunction.homEquiv _ _) h) ≫
        (g.ordinaryPushEvaluation n).hom.app N =
      ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        ((g.ordinaryPullEvaluation n).inv.app M ≫ (SpTowerShriek.ev l E X n).map h) := by
  let P := Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  have hu := SpTowerShriek.geometry_unit_evaluation l E b g n M
  have hu' :
      (SpTowerShriek.ev l E Y n).map (g.ordinaryAdjunction.unit.app M) ≫
          (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) =
        (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((SpTowerShriek.ev l E Y n).obj M) ≫
            P.map ((g.ordinaryPullEvaluation n).inv.app M) := by
    apply (Iso.eq_comp_inv (P.mapIso ((g.ordinaryPullEvaluation n).app M))).2
    simpa only [P, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  change _ ≫ ((g.push ⋙ SpTowerShriek.ev l E Y n).map h ≫ _) = _
  rw [(g.ordinaryPushEvaluation n).hom.naturality h, ← Category.assoc, hu']
  simp only [P, Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_map,
    Category.assoc]

private theorem systemHom_ext {T : Scheme.{u}}
    {M N : Systems T (Arings l E T)} {a b : M ⟶ N}
    (h : ∀ n : ℕ, (SpTowerShriek.ev l E T n).map a =
      (SpTowerShriek.ev l E T n).map b) : a = b := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

/-- The geometric tower operations can be chosen with their ordinary unit and tensor maps.

Source: blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clauses (2)--(4),
and the geometric realization in `sk-lem-sp-tower-bound-operations.proof.md`;
Zheng Construction 4.1, Lemma 4.10; Stacks 03D2, 03EL and 07A4.
(blueprint: lem-sfb-tower-class-tensor-geometry-existence).

Proof: use the coefficient-tower calculus and the ringed sequence site from
strictSystemGeometricRealization. Realize inverse image by the algebraic inverse
image of each constant quotient ring. Choose the constant-section comparison at
each level, so its adjoint is the specified constant direct-image map. Quotient
maps commute with those section maps; hence the unit comparisons assemble to
CoefficientPullback. This constructs a normalized geometry, rather than asserting
an extra normalization for every geometry with the same level functors.
For two ordinary module systems, apply geometricOrdinaryTensor_exists to that
ordinary realization. Its system and system_natural fields provide the assembled
tensor isomorphisms and naturality. Its evaluation and level_pure fields express
the finite maps as the inverse images of pure tensors. Scalar restriction
commutes with that pairing, since both composites send a generalized pure tensor
to the tensor of its two restricted inverse images. Transpose with the ordinary
system adjunction, whose unit evaluates to the finite unit: a pure tensor maps
to the tensor of the two unit sections. This is TensorPullback.normalization.
The construction uses the unital constant-ring comparison also on empty charts;
no nonempty-chart assumption or flatness of a quotient-ring map is needed.
There is no roots-of-unity line, twisting equivalence, or projection assertion here.
-/
theorem exists_tensorGeometry {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : SpTowerShriek.Base l E, ∃ g : SpTowerShriek.Geometry l E b f,
      Nonempty (CoefficientPullback l E b f g) ∧ Nonempty (TensorPullback l E f g) := by
  classical
  obtain ⟨b, g, hpush, δ, hδ, pδ⟩ := exists_unitLevelCoordinates l E f
  obtain ⟨e, he⟩ := SemilinearSections.systemIsoOfEvaluation_exists.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) δ hδ
  have pc : CoefficientPullback l E b f g :=
    { iso := e
      normalization := by
        intro n U x x' hx
        have ha := congrArg (fun k ↦ k.val.app U x') (adjoint_evaluation l E g e.hom n)
        rw [he] at ha
        exact (heq_of_eq ha).trans (pδ n U x x' hx) }
  obtain ⟨μ, hμ, nμ, pμ⟩ := exists_tensorLevelCoordinates l E g hpush
  have hex (M N : Systems Y (Arings l E Y)) :=
    SemilinearSections.systemIsoOfEvaluation_exists.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      (μ M N) (hμ M N)
  choose k hk using hex
  let κ (N : Systems Y (Arings l E Y)) :
      tensorRight l E Y N ⋙ g.pull ≅ g.pull ⋙ tensorRight l E X (g.pull.obj N) :=
    NatIso.ofComponents (fun M ↦ k M N) (by
      intro M M' a
      apply systemHom_ext l E
      intro n
      rw [Functor.map_comp, Functor.map_comp, hk, hk]
      exact nμ N a n)
  refine ⟨b, g, ⟨pc⟩, ⟨{ iso := κ, normalization := ?_ }⟩⟩
  intro M N n U x y
  have ha := congrArg (fun k ↦ k.val.app U
    (tensorPure l E Y M N (op (n, U.unop)) x y))
      (adjoint_evaluation l E g (k M N).hom n)
  rw [hk] at ha
  exact (heq_of_eq ha).trans (pμ M N n U x y)

end AlgebraicGeometry.ProEtale.SpTowerClasses
