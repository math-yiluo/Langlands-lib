/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementStage
import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import all WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageAssembly
import all WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence

/-! Assembly of compatible finite split replacement stages.
The proof reuses the matching and transport helpers of the unconstrained assembly
and the generic tower construction in `SiteFiniteBasisHypercoverExistence`.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Compatible finite replacement stages give a finite split replacement.
Source: Stacks 0DAV, passage from compatible skeleta to a simplicial object.
Every object and every operator is read at a stage containing its degrees.
The compatibility equalities show that this value is independent of the stage;
all simplicial identities and the refinement naturality are checked at a common
finite stage. Splitting, finiteness and the matching universal property in a fixed
degree are the corresponding properties of that finite stage. The object and refinement
component in degree n are read
at stage n, so the finite cofan and sieve membership supplied by hA n transfer
without any change of objects or maps.
(auxiliary; not a blueprint node) -/
theorem exists_local_replacement_of_stage_tower
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (A : ∀ n, FiniteSplitReplacementStage K n)
    (e : ∀ n, (A (n + 1)).restrict n (Nat.le_succ n) = A n)
    (S : ∀ n : ℕ, Sieve (K.obj (op (SimplexCategory.mk n))))
    (hA : ∀ n, StageSolves K S (A n)) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.simplicial ⟶ K),
      ∀ n : ℕ, ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n))),
        Nonempty (IsColimit (Cofan.mk _ ι)) ∧
          ∀ i, S n (ι i ≫ f.app (op (SimplexCategory.mk n))) := by
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
    finite_each_degree := fun n ↦ (A n).U.finite_each_degree ⟨n, Nat.lt_succ_self n⟩ },
    { app := F, naturality := fun {Δ₁ Δ₂} p ↦ hnat Δ₁ Δ₂ p }, ?_⟩
  intro n
  exact hA n ⟨n, Nat.lt_succ_self n⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
