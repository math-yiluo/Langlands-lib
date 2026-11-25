/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData

/-! # Evaluation of the normalized ordinary tower unit

Source: blueprint operations proof (2), evaluated transposes of levelwise units.
(blueprint: lem-sp-tower-ordinary-unit-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Equality elimination for the coefficient-dependent ordinary adjunction data.
private theorem transport_unit_evaluation (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = B l E X) (hτ : HEq τ' (tau l E X))
    (F : S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ')
    (G : SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' ⥤ S l E Y)
    (hF : HEq g.pull F) (hG : HEq g.push G)
    (a : F ⊣ G) (ha : HEq g.ordinaryAdjunction a)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (B' n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P))
    (cF : F ⋙ SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' n ≅ ev l E Y n ⋙ q.1)
    (cG : G ⋙ ev l E Y n ≅ SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' n ⋙ q.2.1)
    (hcF : HEq (g.ordinaryPullEvaluation n) cF)
    (hcG : HEq (g.ordinaryPushEvaluation n) cG)
    (M : S l E Y)
    (h : (ev l E Y n).map (a.unit.app M) ≫ cG.hom.app (F.obj M) ≫
      q.2.1.map (cF.hom.app M) = q.2.2.unit.app ((ev l E Y n).obj M)) :
    (ev l E Y n).map (g.ordinaryAdjunction.unit.app M) ≫
      (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) ≫
      (proEtaleConstantRingPushforward (R l E n) f).map
        ((g.ordinaryPullEvaluation n).hom.app M) =
      (proEtaleConstantRingAdjunction (R l E n) f).unit.app ((ev l E Y n).obj M) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  cases eq_of_heq hG
  cases eq_of_heq ha
  cases eq_of_heq hq
  cases eq_of_heq hcF
  cases eq_of_heq hcG
  exact h

/-- Evaluation carries the normalized ordinary system unit to the constant-ring
unit, after the specified push and pull comparisons.

Source: blueprint operations proof (2), paragraph on transposes of levelwise units;
`SemilinearSections.Geometry.ordinary_unit_evaluation` and the normalization fields
of `SpTowerShriek.Geometry`.
(blueprint: lem-sp-tower-ordinary-unit-evaluation).

Proof: identify the generic coefficient family with B using Geometry.coefficients,
and the generic transition family with tau using Geometry.transitions. This
identifies the two system categories and their evaluations. Under these coordinate
identifications, Geometry.pull_eq and Geometry.push_eq identify the ordinary
functors, and Geometry.ordinaryAdjunction_eq identifies their specified adjunction.
Apply generic.ordinary_unit_evaluation to M at n. Replace the two component
comparisons by Geometry.ordinaryPullEvaluation_eq and
Geometry.ordinaryPushEvaluation_eq, and the finite adjunction by
Geometry.levelAdjunction_eq. The resulting equation is the one displayed here:
the evaluated system unit, followed by the push comparison and the pushforward of
the pull comparison, is the finite unit. These are equalities of ordinary module
maps, so no derived faithfulness or exactness assertion is involved. The argument
works also at n = 0, on the empty scheme and on the zero system. -/
theorem geometry_unit_evaluation (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ) (M : S l E Y) :
    (ev l E Y n).map (g.ordinaryAdjunction.unit.app M) ≫
      (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) ≫
      (proEtaleConstantRingPushforward (R l E n) f).map
        ((g.ordinaryPullEvaluation n).hom.app M) =
      (proEtaleConstantRingAdjunction (R l E n) f).unit.app ((ev l E Y n).obj M) := by
  exact transport_unit_evaluation l E b g n
    g.generic.coefficients g.generic.coefficientTransition g.coefficients g.transitions
    g.generic.pull g.generic.push g.pull_eq g.push_eq
    g.generic.ordinaryAdjunction g.ordinaryAdjunction_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n)
    (g.generic.ordinaryPullEvaluation n) (g.generic.ordinaryPushEvaluation n)
    (g.ordinaryPullEvaluation_eq n) (g.ordinaryPushEvaluation_eq n) M
    (g.generic.ordinary_unit_evaluation n M)

end AlgebraicGeometry.ProEtale.SpTowerShriek
