/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
/-! # Finite truncations of finite split étale hypercovers -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover
variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Retain all hypercover data through a fixed degree.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
Restrict all simplicial, nondegenerate and matching data. Reindex the full splitting cofan by the
finite set of retained degrees and epimorphisms from the given simplex: an epimorphism forces the
target degree not to exceed the source degree. The inverse reindexing inserts that bound, giving
the same colimit universal property. Restrict matching cones to retained simplices and extend
their indices back to the full lower-degree category; the original matching universal property
supplies exactly the required lift and uniqueness.
(auxiliary; not a blueprint node) -/
noncomputable def finiteTruncation (U : FiniteSplitEtaleHypercover X) (r : ℕ) :
    TruncatedFiniteSplitEtaleHypercover X r where
  simplicial := (SimplicialObject.truncation r).obj U.simplicial
  N n := U.splitting.N n.val
  inclusion n := U.splitting.ι n.val
  splitting Δ := by
    let old := U.splitting.isColimit' (op Δ.unop.obj)
    let lower (a : SimplicialObject.Splitting.IndexSet (op Δ.unop.obj)) :
        Σ n : Fin (r + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk n.val // Epi α} :=
      ⟨⟨a.1.unop.len, Nat.lt_succ_of_le
        ((by have := a.2.property; exact SimplexCategory.len_le_of_epi a.e :
          a.1.unop.len ≤ Δ.unop.obj.len).trans Δ.unop.property)⟩, a.2⟩
    let large (a : Σ n : Fin (r + 1),
        {α : Δ.unop.obj ⟶ SimplexCategory.mk n.val // Epi α}) :
        SimplicialObject.Splitting.IndexSet (op Δ.unop.obj) :=
      ⟨op (SimplexCategory.mk a.1.val), a.2⟩
    refine Cofan.IsColimit.mk _ (fun s ↦
      Cofan.IsColimit.desc old (fun a ↦ s.inj (lower a))) ?_ ?_
    · intro s a
      exact Cofan.IsColimit.fac old _ (large a)
    · intro s f hf
      apply Cofan.IsColimit.hom_ext old
      intro a
      rw [Cofan.IsColimit.fac]
      exact hf (lower a)
  finite_each_degree n := U.finite_each_degree n.val
  matching n := U.matching n.val
  projection n Δ h θ := U.projection n.val Δ.obj h θ
  projection_naturality n Δ Δ' h h' α θ :=
    U.projection_naturality n.val Δ.obj Δ'.obj h h' α.hom θ
  matching_universal n T p hp := by
    let p' (Δ : SimplexCategory) (h : Δ.len < n.val)
        (θ : Δ ⟶ SimplexCategory.mk n.val) :=
      p ⟨Δ, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ n.isLt)⟩ h θ
    have hp' : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n.val)
        (h' : Δ'.len < n.val) (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n.val),
        p' Δ h θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
          p' Δ' h' (α ≫ θ) := by
      intro Δ Δ' h h' α θ
      exact hp _ _ h h' (SimplexCategory.Truncated.Hom.tr α _ _) θ
    obtain ⟨f, hf, huniq⟩ := U.matching_universal n.val T p' hp'
    refine ⟨f, ?_, ?_⟩
    · intro Δ h θ
      exact hf Δ.obj h θ
    · intro g hg
      apply huniq g
      intro Δ h θ
      exact hg ⟨Δ, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ n.isLt)⟩ h θ
  matchingMap n := U.matchingMap n.val
  matchingMap_projection n Δ h θ := U.matchingMap_projection n.val Δ.obj h θ
  matching_cover n := U.matching_cover n.val

end AlgebraicGeometry.FiniteSplitEtaleHypercover
