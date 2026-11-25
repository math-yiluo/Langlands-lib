/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.HypercoverStageTowerTruncation
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageExtension
/-! # Relative extension retaining the initial map -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- A finite replacement stage extends, retaining its simplicial map in all initial degrees.
Source: Stacks 0DAV, relative split hypercover induction. Repeatedly apply the
one-stage relative extension, restrict to diagonal degrees, and assemble the tower.
The tower's initial restriction equality identifies both the skeleton and its map.
(auxiliary; not a blueprint node) -/
theorem exists_extension_of_replacement_stage
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K) (r : ℕ)
    (R : FiniteSplitReplacementStage K r) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.simplicial ⟶ K)
      (e : (SimplicialObject.truncation r).obj V.simplicial ≅ R.U.simplicial),
      (SimplicialObject.truncation r).map f = e.hom ≫ R.f := by
  classical
  have hstep (n : ℕ) (T : FiniteSplitReplacementStage K n) :=
    exists_replacement_stage_extension K hK n T
  choose next hnext using hstep
  let B : ∀ n, FiniteSplitReplacementStage K (r + n) :=
    Nat.rec R (fun n T ↦ next (r + n) T)
  have hB (n : ℕ) :
      (B n).restrict r (Nat.le_add_right r n) = R := by
    induction n with
    | zero => exact R.restrict_self
    | succ n ih =>
      rw [show B (n + 1) = next (r + n) (B n) from rfl,
        ← FiniteSplitReplacementStage.restrict_restrict _
          (Nat.le_add_right r n) (Nat.le_succ (r + n)), hnext]
      exact ih
  let T (n : ℕ) : FiniteSplitReplacementStage K n :=
    (B n).restrict n (Nat.le_add_left n r)
  have hT (n : ℕ) : (T (n + 1)).restrict n (Nat.le_succ n) = T n := by
    dsimp only [T]
    rw [FiniteSplitReplacementStage.restrict_restrict,
      ← FiniteSplitReplacementStage.restrict_restrict _
        (Nat.le_add_left n r) (Nat.le_succ (r + n)),
      show B (n + 1) = next (r + n) (B n) from rfl, hnext]
  obtain ⟨V, f, hV, hf⟩ := exists_hypercover_of_stage_tower_with_truncation K T hT
  have hR : T r = R := hB r
  have hsim : (SimplicialObject.truncation r).obj V.simplicial = R.U.simplicial :=
    (hV r).trans (congrArg (fun Z ↦ Z.U.simplicial) hR)
  refine ⟨V, f, eqToIso hsim, ?_⟩
  have transport (P Q : FiniteSplitReplacementStage K r) (h : P = Q) :
      eqToHom (congrArg (fun Z ↦ Z.U.simplicial) h) ≫ Q.f = P.f := by
    subst Q
    simp
  have hh := transport (T r) R hR
  rw [hf, ← hh]
  simp only [← Category.assoc, eqToHom_trans]
  rfl

end AlgebraicGeometry.FiniteSplitEtaleHypercover
