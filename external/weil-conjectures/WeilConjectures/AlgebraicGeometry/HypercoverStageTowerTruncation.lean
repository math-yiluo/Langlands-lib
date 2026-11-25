/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import all WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageAssembly
import all WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
/-! # Assembly retaining the prescribed finite skeleta -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible finite replacement stages assemble without changing any finite skeleton.
Source: Stacks 0DAV, assembly of split skeleta. Read each object and operator at
any stage containing its degrees. Compatibility identifies these choices; the
simplicial identities, splitting and matching properties are checked at that stage.
(auxiliary; not a blueprint node) -/
theorem exists_hypercover_of_stage_tower_with_truncation
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (A : ∀ n, FiniteSplitReplacementStage K n)
    (e : ∀ n, (A (n + 1)).restrict n (Nat.le_succ n) = A n) :
    ∃ V : FiniteSplitEtaleHypercover X,
      ∃ (f : V.simplicial ⟶ K)
        (hV : ∀ n, (SimplicialObject.truncation n).obj V.simplicial = (A n).U.simplicial),
        ∀ n, (SimplicialObject.truncation n).map f = eqToHom (hV n) ≫ (A n).f := by
  classical
  let k (n : ℕ) := (A n).U.simplicial
  have ee (n : ℕ) :
      (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj (k (n + 1)) = k n :=
    congrArg (fun B ↦ B.U.simplicial) (e n)
  let S := towerGlue k ee
  let N (n : ℕ) := (A n).U.N ⟨n, Nat.lt_succ_self n⟩
  let ι (n : ℕ) : N n ⟶ S.obj (op (SimplexCategory.mk n)) :=
    (A n).U.inclusion ⟨n, Nat.lt_succ_self n⟩
  have hN (n m : ℕ) (h : m ≤ n) :
      N m = (A n).U.N ⟨m, Nat.lt_succ_of_le h⟩ :=
    congrArg (fun B ↦ B.U.N ⟨m, Nat.lt_succ_self m⟩)
      (stage_restrict A e n m h).symm
  have hι (n m : ℕ) (h : m ≤ n) :
      ι m ≫ eqToHom (towerObj_eq k ee (op (SimplexCategory.mk m)) n h) =
        eqToHom (hN n m h) ≫ (A n).U.inclusion ⟨m, Nat.lt_succ_of_le h⟩ := by
    have hi := inclusion_congr ((A n).restrict m h) (A m)
      (stage_restrict A e n m h) ⟨m, Nat.lt_succ_self m⟩
    have ht := congrArg (fun t ↦ eqToHom (hN n m h) ≫ t ≫
      eqToHom (towerObj_eq k ee (op (SimplexCategory.mk m)) n h)) hi
    simpa only [FiniteSplitReplacementStage.restrict,
      TruncatedFiniteSplitEtaleHypercover.restrict, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id] using ht
  let F (Δ : SimplexCategoryᵒᵖ) : S.obj Δ ⟶ K.obj Δ :=
    (A Δ.unop.len).f.app (op ⟨Δ.unop, le_rfl⟩)
  have hF (Δ : SimplexCategoryᵒᵖ) (n : ℕ) (h : Δ.unop.len ≤ n) :
      F Δ = eqToHom (towerObj_eq k ee Δ n h) ≫
        (A n).f.app (op ⟨Δ.unop, h⟩) := by
    have hf := refinement_congr ((A n).restrict Δ.unop.len h) (A Δ.unop.len)
      (stage_restrict A e n Δ.unop.len h) (op ⟨Δ.unop, le_rfl⟩)
    have ht := congrArg (fun t ↦ eqToHom (towerObj_eq k ee Δ n h) ≫ t) hf
    dsimp only [FiniteSplitReplacementStage.restrict] at ht
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at ht
    exact ht
  have hnat : ∀ (Δ₁ Δ₂ : SimplexCategoryᵒᵖ) (p : Δ₁ ⟶ Δ₂),
      S.map p ≫ F Δ₂ = F Δ₁ ≫ K.map p := by
    intro Δ₁ Δ₂ p
    let n := max Δ₁.unop.len Δ₂.unop.len
    have h₁ : Δ₁.unop.len ≤ n := le_max_left _ _
    have h₂ : Δ₂.unop.len ≤ n := le_max_right _ _
    rw [hF Δ₁ n h₁, hF Δ₂ n h₂]
    change (eqToHom _ ≫ (k n).map
      (SimplexCategory.Truncated.Hom.tr p.unop h₂ h₁).op ≫ eqToHom _) ≫
        (eqToHom _ ≫ _) = _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have ht := (A n).f.naturality
      (SimplexCategory.Truncated.Hom.tr p.unop h₂ h₁).op
    change (k n).map (SimplexCategory.Truncated.Hom.tr p.unop h₂ h₁).op ≫
      (A n).f.app (op ⟨Δ₂.unop, h₂⟩) =
        (A n).f.app (op ⟨Δ₁.unop, h₁⟩) ≫ K.map p at ht
    exact congrArg (fun t ↦ eqToHom (towerObj_eq k ee Δ₁ n h₁) ≫ t) ht
  have hsplit : ∀ Δ : SimplexCategoryᵒᵖ,
      IsColimit (SimplicialObject.Splitting.cofan' N S ι Δ) := by
    intro Δ
    let d := Δ.unop.len
    let Δ' : (SimplexCategory.Truncated d)ᵒᵖ := op ⟨Δ.unop, le_rfl⟩
    let J := Σ q : Fin (d + 1),
      {α : Δ.unop ⟶ SimplexCategory.mk q.val // Epi α}
    let bound (a : SimplicialObject.Splitting.IndexSet Δ) : a.1.unop.len ≤ d := by
      have := a.2.property
      exact SimplexCategory.len_le_of_epi a.e
    let small (a : SimplicialObject.Splitting.IndexSet Δ) : J :=
      ⟨⟨a.1.unop.len, Nat.lt_succ_of_le (bound a)⟩, a.2⟩
    let large (a : J) : SimplicialObject.Splitting.IndexSet Δ :=
      ⟨op (SimplexCategory.mk a.1.val), a.2⟩
    let old := (A d).U.splitting Δ'
    have hinj (a : SimplicialObject.Splitting.IndexSet Δ) :
        (SimplicialObject.Splitting.cofan' N S ι Δ).inj a =
          eqToHom (hN d a.1.unop.len (bound a)) ≫
            (A d).U.inclusion (small a).1 ≫ (k d).map
              (SimplexCategory.Truncated.Hom.tr a.e le_rfl (bound a)).op := by
      change ι a.1.unop.len ≫ towerMapAt k ee a.e.op
        (max a.1.unop.len d) (le_max_left _ _) (le_max_right _ _) = _
      rw [towerMapAt_eq k ee a.e.op _ d _ _ (bound a) le_rfl]
      change ι a.1.unop.len ≫ eqToHom _ ≫ _ ≫ eqToHom _ = _
      rw [← Category.assoc, hι d a.1.unop.len (bound a)]
      simp only [Category.assoc, eqToHom_refl, Category.comp_id]
      rfl
    refine Cofan.IsColimit.mk _ (fun t ↦
      Cofan.IsColimit.desc old (fun a : J ↦
        eqToHom (hN d a.1.val (Nat.le_of_lt_succ a.1.isLt)).symm ≫
          t.inj (large a))) ?_ ?_
    · intro t a
      rw [hinj]
      have ht := congrArg (fun z ↦ eqToHom (hN d a.1.unop.len (bound a)) ≫ z)
        (Cofan.IsColimit.fac old
          (fun b : J ↦
            eqToHom (hN d b.1.val (Nat.le_of_lt_succ b.1.isLt)).symm ≫
              t.inj (large b)) (small a))
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp] at ht
      exact ht
    · intro t f hf
      apply Cofan.IsColimit.hom_ext old
      intro a
      rw [Cofan.IsColimit.fac]
      have ht := congrArg (fun z ↦
        eqToHom (hN d a.1.val (Nat.le_of_lt_succ a.1.isLt)).symm ≫ z)
          (hf (large a))
      rw [hinj] at ht
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp] at ht
      exact ht
  have hCov : IsEtaleHypercover S := by
    intro n
    exact matching_of_truncation S n (A n).U (towerGlue_restrict k ee n).symm
  choose M π μ hn hu hp hc using hCov
  refine ⟨{
    simplicial := S
    splitting := ⟨N, ι, hsplit⟩
    matching := M
    projection := π
    projection_naturality := hn
    matching_universal := hu
    matchingMap := μ
    matchingMap_projection := hp
    matching_cover := hc
    finite_each_degree := ?_ },
    { app := F, naturality := fun {Δ₁ Δ₂} p ↦ hnat Δ₁ Δ₂ p },
    fun n ↦ towerGlue_restrict k ee n, ?_⟩
  · intro n
    exact (A n).U.finite_each_degree ⟨n, Nat.lt_succ_self n⟩
  · intro n
    ext Δ
    simp only [NatTrans.comp_app, eqToHom_app]
    change F (op Δ.unop.obj) = eqToHom _ ≫ (A n).f.app Δ
    exact hF (op Δ.unop.obj) n Δ.unop.property


end AlgebraicGeometry.FiniteSplitEtaleHypercover
