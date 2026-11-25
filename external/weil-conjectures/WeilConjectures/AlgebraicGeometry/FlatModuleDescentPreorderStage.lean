/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.FlatModuleDescent

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- A strictly increasing auxiliary level makes the preorder antisymmetric without
-- identifying any of its objects. Projection is surjective and final.
private def FlatStageIndex (I : Type u) := I × ℕ

private instance {I : Type u} [Preorder I] : PartialOrder (FlatStageIndex I) where
  le a b := a = b ∨ (a.1 ≤ b.1 ∧ a.2 < b.2)
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | ⟨hab, hn⟩
    · exact hbc
    rcases hbc with rfl | ⟨hbc, hm⟩
    · exact Or.inr ⟨hab, hn⟩
    · exact Or.inr ⟨hab.trans hbc, hn.trans hm⟩
  le_antisymm a b hab hba := by
    rcases hab with h | ⟨_, hn⟩
    · exact h
    rcases hba with h | ⟨_, hm⟩
    · exact h.symm
    · exact False.elim (Nat.lt_asymm hn hm)

private instance {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] :
    IsDirectedOrder (FlatStageIndex I) where
  directed a b := by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.1 b.1
    refine ⟨(k, max a.2 b.2 + 1), Or.inr ⟨ha, ?_⟩, Or.inr ⟨hb, ?_⟩⟩
    · exact Nat.lt_succ_of_le (le_max_left _ _)
    · exact Nat.lt_succ_of_le (le_max_right _ _)

private theorem flatStageProjection_mono {I : Type u} [Preorder I] :
    Monotone (fun a : FlatStageIndex I ↦ a.1) := by
  intro a b h
  rcases h with rfl | h
  · exact le_rfl
  · exact h.1

/-- Flatness at the limit descends to one canonical stage of a directed preorder.

Source: Stacks Project, limits.tex, Tag 05LY; categories.tex, Tag 0032.
(blueprint: lem-pc-flat-module-descent-preorder-stage).

Proof: i makes the directed thin category nonempty and filtered. By Tag 0032 choose
a nonempty directed partial order J and a final functor F : J -> I. Finality supplies
t in J and a morphism i -> F(t). Pull M back to the canonical base change at F(t).
Finite presentation of the morphism and module is preserved by base change, and
finite presentation supplies quasi-coherence. Restrict R and c along F and F.op;
initiality of F.op preserves the limiting cone with the same affine vertex.
Cartesian pasting, tensor-pullback composition and the comparison of cartesian
models identify its limit module with the original one, hence it is relatively flat.
Apply partial-order flat-module descent (Tag 05LY) to obtain s >= t at which this
module is flat. Put j = F(s). Functoriality gives i <= j. Pasting and tensor-pullback
composition identify the stage module with the canonical pullback of M from i to j;
cartesian-model comparison transfers its relative flatness. This concludes existence
at one stage; propagation to later original stages is not part of this lemma.
Empty source schemes and the zero module remain flat. The object i rules out an
empty index category; antisymmetry of I and flat transition maps are not needed. -/
theorem exists_isFlatOver_of_isPullback_limit_preorder_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation]
    (hflat : ((Scheme.Modules.tensorPullback
      (pullback.fst f (c.π.app (op i)))).obj M).IsFlatOver
      (pullback.snd f (c.π.app (op i)))) :
    ∃ (j : I) (hij : i ≤ j),
      ((Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj M).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij)))) := by
  let F : FlatStageIndex I ⥤ I := flatStageProjection_mono.functor
  have : F.Final := flatStageProjection_mono.final_functor_iff.mpr
    (fun k ↦ ⟨(k, 0), le_rfl⟩)
  let c' : Cone ((F ⋙ R).op ⋙ Scheme.Spec) := c.whisker F.op
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  let t : FlatStageIndex I := (i, 0)
  let : IsAffine c'.pt := inferInstanceAs (IsAffine c.pt)
  let : ∀ k : FlatStageIndex I, IsNoetherianRing ((F ⋙ R).obj k) :=
    fun k ↦ inferInstanceAs (IsNoetherianRing (R.obj k.1))
  obtain ⟨s, hts, hs⟩ := exists_eventually_isFlatOver_of_limit
    (F ⋙ R) c' hc' t f M hflat
  refine ⟨s.1, flatStageProjection_mono hts, ?_⟩
  exact hs s le_rfl

end AlgebraicGeometry
