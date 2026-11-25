/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientScalarComparison

/-! # Root normalization of the finite additive coordinate

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-coefficient-root-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] finiteScalarLineCoordinate finiteScalarComparison
  cartierRootsComparison Functor.mapDerivedCategory

/-- The line coordinate carries the comparison image of root scalar extension
to the actual finite root map. Source: diagonal-tower trace (1), root-section
normalization of the coefficient coordinates
(blueprint: lem-sfb-finite-coefficient-root-coordinate).

Proof: apply the site-comparison adjunction, so it suffices to test etale root
sections. Naturality of its unit moves scalar extension to the section before
the unit. The mate equation for forgetting coefficients and the actual
associated-module-sheaf unit identify its image with the scalar-unit section of
one tensor the root. Apply line_sections with the identity restriction. The
right side is the same tensor by the defining finiteRootMap equation and the
roots comparison. The argument uses all root sections and includes zero rings
and empty schemes. -/
theorem finiteScalarLineCoordinate_root (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
        (Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n)) T) ≫
        finiteScalarLineCoordinate l E n T c =
      cartierRootsComparison T (l ^ (n + 1)) ≫ finiteRootMap l E T n := by
  let r := Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
    (ULift.ext (coefficient_annihilates l E n)) T
  apply ((comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext U z
  have hn := (comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.naturality r
  have hnz := congrArg (fun f ↦ f.hom.app U z) hn
  have hc := c.line_sections U ((Scheme.toProEt T).op.obj U) (𝟙 _) 1 z
  have hr := (Classical.choose_spec (finiteRootMap_existsUnique l E T n).exists)
    ((Scheme.toProEt T).op.obj U)
    ((cartierRootsComparison T (l ^ (n + 1))).hom.app ((Scheme.toProEt T).op.obj U)
      (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        (T.rootsOfUnitySheaf (l ^ (n + 1)))).hom.app U z))
  have hnz' :
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).map r).hom.app
          ((Scheme.toProEt T).op.obj U)
          (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf (l ^ (n + 1)))).hom.app U z) =
        (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
            (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
              (ULift.ext (coefficient_annihilates l E n))))).hom.app U
                (r.hom.app U z)) := hnz.symm
  unfold finiteScalarLineCoordinate
  change c.line.hom.val.app ((Scheme.toProEt T).op.obj U)
      (((finiteScalarComparison l E n T).hom.app _).hom.app
        ((Scheme.toProEt T).op.obj U)
        (((comparisonUpperStar AddCommGrpCat.{u + 1} T).map r).hom.app
          ((Scheme.toProEt T).op.obj U)
          (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf (l ^ (n + 1)))).hom.app U z))) =
    (finiteRootMap l E T n).hom.app ((Scheme.toProEt T).op.obj U)
      ((cartierRootsComparison T (l ^ (n + 1))).hom.app ((Scheme.toProEt T).op.obj U)
        (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          (T.rootsOfUnitySheaf (l ^ (n + 1)))).hom.app U z))
  rw [hnz', finiteScalarComparison_unit_section]
  have hgen : r.hom.app U z =
      Scheme.finiteEtaleTateOneGenerator (FiniteRing l E n) (l ^ (n + 1)) T
        (ULift.ext (coefficient_annihilates l E n)) U 1 z := rfl
  have hroots : (cartierRootsIso T (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hT).hom =
        cartierRootsComparison T (l ^ (n + 1)) := by
    unfold cartierRootsIso
    rfl
  have hm := ((comparisonUpperStar (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) T).obj
    (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (SpTowerP1.levelRing l E n)
      (SpTowerP1.levelAnnihilates l E n))).obj.map_id ((Scheme.toProEt T).op.obj U)
  have ha := ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
    (T.rootsOfUnitySheaf (l ^ (n + 1)))).obj.map_id ((Scheme.toProEt T).op.obj U)
  simp only [op_id, op_unop, hm, ha, map_one, hroots] at hc
  exact hc.trans hr.symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
