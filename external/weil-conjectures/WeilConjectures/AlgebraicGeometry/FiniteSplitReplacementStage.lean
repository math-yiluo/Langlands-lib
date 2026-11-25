/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover

/-! Finite stages of a split replacement, following Stacks 0DAV. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace TruncatedFiniteSplitEtaleHypercover

/-- Restriction retains precisely the data in degrees at most `m`.
Source: Stacks 0DAV (auxiliary; not a blueprint node). -/
def restrict {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (m : ℕ) (hm : m ≤ n) :
    TruncatedFiniteSplitEtaleHypercover X m where
  simplicial := (SimplicialObject.Truncated.trunc X.Etale n m hm).obj U.simplicial
  N q := U.N ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
  inclusion q := U.inclusion ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
  splitting Δ := by
    let Δ' : (SimplexCategory.Truncated n)ᵒᵖ :=
      op ⟨Δ.unop.obj, Δ.unop.property.trans hm⟩
    let old := U.splitting Δ'
    let lower (a : Σ q : Fin (n + 1),
        {α : Δ.unop.obj ⟶ SimplexCategory.mk q.val // Epi α}) :
        Σ q : Fin (m + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk q.val // Epi α} :=
      ⟨⟨a.1.val, Nat.lt_succ_of_le
        ((by have := a.2.property; exact SimplexCategory.len_le_of_epi a.2.val :
          a.1.val ≤ Δ.unop.obj.len).trans
          Δ.unop.property)⟩, a.2⟩
    refine Cofan.IsColimit.mk _ (fun s ↦
      Cofan.IsColimit.desc old (fun a ↦ s.inj (lower a))) ?_ ?_
    · intro s a
      exact Cofan.IsColimit.fac old _ ⟨
        ⟨a.1.val, lt_of_lt_of_le a.1.isLt (Nat.succ_le_succ hm)⟩, a.2⟩
    · intro s f hf
      apply Cofan.IsColimit.hom_ext old
      intro a
      rw [Cofan.IsColimit.fac]
      exact hf (lower a)
  finite_each_degree q :=
    U.finite_each_degree ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
  matching q := U.matching ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
  projection q Δ h θ := U.projection
    ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
    ⟨Δ.obj, Δ.property.trans hm⟩ h θ
  projection_naturality q Δ Δ' h h' α θ := U.projection_naturality
    ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
    ⟨Δ.obj, Δ.property.trans hm⟩ ⟨Δ'.obj, Δ'.property.trans hm⟩ h h'
    (SimplexCategory.Truncated.Hom.tr α.hom
      (Δ'.property.trans hm) (Δ.property.trans hm)) θ
  matching_universal q T p hp := by
    let p' (Δ : SimplexCategory.Truncated n) (h : Δ.obj.len < q.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk q.val) :=
      p ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
    have hp' : ∀ (Δ Δ' : SimplexCategory.Truncated n)
        (h : Δ.obj.len < q.val) (h' : Δ'.obj.len < q.val) (α : Δ' ⟶ Δ)
        (θ : Δ.obj ⟶ SimplexCategory.mk q.val),
        p' Δ h θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
          p' Δ' h' (α.hom ≫ θ) := by
      intro Δ Δ' h h' α θ
      exact hp _ _ h h' (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
    obtain ⟨f, hf, huniq⟩ := U.matching_universal
      ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩ T p' hp'
    refine ⟨f, ?_, ?_⟩
    · intro Δ h θ
      exact hf ⟨Δ.obj, Δ.property.trans hm⟩ h θ
    · intro g hg
      apply huniq g
      intro Δ h θ
      exact hg ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
  matchingMap q := U.matchingMap
    ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
  matchingMap_projection q Δ h θ := U.matchingMap_projection
    ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩
    ⟨Δ.obj, Δ.property.trans hm⟩ h θ
  matching_cover q := U.matching_cover
    ⟨q.val, lt_of_lt_of_le q.isLt (Nat.succ_le_succ hm)⟩

/-- Restricting to the same bound retains the data. -/
theorem restrict_self {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) : U.restrict n le_rfl = U := by
  cases U
  unfold restrict
  congr 1

/-- Restriction is transitive. -/
theorem restrict_restrict {X : Scheme.{u}} {n m l : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (hml : l ≤ m) (hnm : m ≤ n) :
    (U.restrict m hnm).restrict l hml = U.restrict l (hml.trans hnm) := by
  cases U
  unfold restrict
  congr 1

end TruncatedFiniteSplitEtaleHypercover

/-- A split finite hypercover through degree `n`, together with its map to `K`.
Source: Stacks 0DAV (auxiliary; not a blueprint node). -/
structure FiniteSplitReplacementStage {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    (n : ℕ) where
  U : TruncatedFiniteSplitEtaleHypercover X n
  f : U.simplicial ⟶ (SimplicialObject.truncation n).obj K

namespace FiniteSplitReplacementStage

/-- Restrict both the split data and the refinement morphism.
Source: Stacks 0DAV (auxiliary; not a blueprint node). -/
def restrict {X : Scheme.{u}} {K : SimplicialObject X.Etale} {n : ℕ}
    (A : FiniteSplitReplacementStage K n) (m : ℕ) (hm : m ≤ n) :
    FiniteSplitReplacementStage K m where
  U := A.U.restrict m hm
  f := (SimplicialObject.Truncated.trunc X.Etale n m hm).map A.f

/-- Restricting to the same bound retains replacement data. -/
theorem restrict_self {X : Scheme.{u}} {K : SimplicialObject X.Etale} {n : ℕ}
    (A : FiniteSplitReplacementStage K n) : A.restrict n le_rfl = A := by
  cases A with
  | mk U f =>
    simp only [restrict]
    congr 1

/-- Restriction of replacement data is transitive. -/
theorem restrict_restrict {X : Scheme.{u}} {K : SimplicialObject X.Etale}
    {n m l : ℕ} (A : FiniteSplitReplacementStage K n) (hml : l ≤ m) (hnm : m ≤ n) :
    (A.restrict m hnm).restrict l hml = A.restrict l (hml.trans hnm) := by
  cases A with
  | mk U f =>
    simp only [restrict]
    congr 1

end FiniteSplitReplacementStage
/-- Matching data for the next degree of a finite stage, universal among all schemes over X.
Source: Stacks 0DAV (auxiliary; not a blueprint node). -/
structure ReplacementBoundary {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) where
  M : X.Etale
  π : ∀ (Δ : SimplexCategory.Truncated n),
    (Δ.obj ⟶ SimplexCategory.mk (n + 1)) → (M ⟶ U.simplicial.obj (op Δ))
  naturality : ∀ (Δ Δ' : SimplexCategory.Truncated n) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
    π Δ θ ≫ U.simplicial.map α.op = π Δ' (α.hom ≫ θ)
  universal : ∀ (T : Over X)
    (p : ∀ (Δ : SimplexCategory.Truncated n),
      (Δ.obj ⟶ SimplexCategory.mk (n + 1)) →
        (T ⟶ (Scheme.Etale.forget X).obj (U.simplicial.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory.Truncated n) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      p Δ θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
        p Δ' (α.hom ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj M,
      ∀ (Δ : SimplexCategory.Truncated n) (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
        f ≫ (Scheme.Etale.forget X).map (π Δ θ) = p Δ θ
  compact : CompactSpace M.left
  quasiSeparated : QuasiSeparatedSpace M.left

end AlgebraicGeometry
