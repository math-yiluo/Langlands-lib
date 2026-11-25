/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonPartial
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceOrdinaryLimitEpi
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceUnitComparisonIso
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions

/-! # Milnor invertibility for the diagonal trace comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a b c v w g va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private theorem lineCone_lift_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) :
    IsIso (limit.lift (r.F.obj (lineModule l E c))
      ⟨(diagonalCompletedRestriction l T).obj (Scheme.purTwistZlModule T l),
        a.lineProjection⟩) := by
  let F := diagonalForget l T
  let d : Cone (r.F.obj (lineModule l E c)) := ⟨_, a.lineProjection⟩
  have : F.ReflectsIsomorphisms := by
    dsimp [F, diagonalForget]
    infer_instance
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hc : IsLimit ((Cone.postcompose a.lineForget.hom).obj (F.mapCone d)) := by
    apply (limit.isLimit (roots l T)).ofIsoLimit
    refine Cone.ext (Iso.refl _) ?_
    intro n
    ext U x
    exact (a.line_projection n.unop U x).symm
  have hd : IsLimit d := isLimitOfReflects F
    ((IsLimit.postcomposeHomEquiv a.lineForget (F.mapCone d)) hc)
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit _)).mp ⟨hd⟩

@[instance_reducible] private def residueInvertible (l : ℕ) (T : Scheme.{u})
    (h : IsUnit (l : Γ(T, ⊤))) : ∀ x : T, Invertible (l : T.residueField x) := by
  intro x
  let ψ := (T.residue x).hom.comp (T.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (l : T.residueField x) from by
    simpa only [map_natCast] using h.map ψ).invertible

attribute [local irreducible] diagonalCompletedRestriction
  Coefficients.lineMap exactConeComparison diagonalOrdinaryRlim

private theorem lineComparison_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] [∀ x : T, Invertible (l : T.residueField x)]
    {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) (L : DiagonalRlim (DiagonalMod l T)) :
    IsIso (a.lineMap l E L) := by
  have hcone := lineCone_lift_isIso l E a
  have hroot (n : ℕ) : Epi ((roots l T).map (homOfLE (Nat.le_succ n)).op) := by
    simpa only [roots, Scheme.proEtaleRootsOfUnityTower,
      Functor.ofOpSequence_map_homOfLE_succ] using
        Scheme.purTwistRootTransitions_epi T l n
  have ht (n : ℕ) : Epi ((r.F.obj (lineModule l E c)).map
      (homOfLE (Nat.le_succ n)).op) :=
    forgottenTower_epi l T _ (towerTransitions_of_iso a.lineForget hroot) n
  have hlim := diagonalOrdinaryRlim_isIso_of_epi l T L _ ht
  unfold Coefficients.lineMap
  exact exactConeComparison_isIso _ _ _ _ _ _ hcone hlim

/-- The two coefficient-cone maps in a partial presentation are invertible.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), the Milnor
comparison for quotient and root towers.
(blueprint: new-sfb-diagonal-trace-comparison-limit-isos).

Proof: the quotient and root transitions are epimorphic, so the Milnor comparison
is an isomorphism. The defining projection equations identify the ordinary limits
with the completed unit and root line, and the derived unit identifies the resulting
maps with the two coefficient cone maps.
-/
theorem diagonalTraceComparisonLimitIsos
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (m : X ≅ ProjectiveLine S)
    (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (p : PartialPresentation l (ULift.{u} (Padic l)) f) :
    IsIso (p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS) ∧
      IsIso (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) := by
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    have h := hS.map (m.hom ≫ (ProjectiveLine S ↘ S)).appTop.hom
    rw [hm] at h
    simpa only [map_natCast] using h
  have : ∀ x : X, Invertible (l : X.residueField x) := residueInvertible l X hX
  exact ⟨diagonalUnitComparison_isIso l (ULift.{u} (Padic l)) p.coefficientsS p.LS,
    lineComparison_isIso l (ULift.{u} (Padic l)) p.coefficientsX p.LX⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
