/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import all WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence

/-! Assembly of compatible finite split replacement stages.
The underlying functor construction uses the proved tower construction in
`WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence`.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

private theorem stage_restrict
    {X : Scheme.{u}} {K : SimplicialObject X.Etale}
    (A : ∀ n, FiniteSplitReplacementStage K n)
    (e : ∀ n, (A (n + 1)).restrict n (Nat.le_succ n) = A n)
    (n m : ℕ) (h : m ≤ n) : (A n).restrict m h = A m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero h
    exact (A 0).restrict_self
  | succ n ih =>
    obtain rfl | h := eq_or_lt_of_le h
    · exact (A (n + 1)).restrict_self
    · rw [← FiniteSplitReplacementStage.restrict_restrict
        (A (n + 1)) (Nat.le_of_lt_succ h) (Nat.le_succ n), e n]
      exact ih m (Nat.le_of_lt_succ h)

private theorem matching_of_truncation
    {X : Scheme.{u}} (S : SimplicialObject X.Etale) (n : ℕ)
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (hU : U.simplicial = (SimplicialObject.truncation n).obj S) :
    ∃ (M : X.Etale)
      (π : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (M ⟶ S.obj (op Δ)))
      (μ : S.obj (op (SimplexCategory.mk n)) ⟶ M),
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        π Δ h θ ≫ S.map α.op = π Δ' h' (α ≫ θ)) ∧
      (∀ (T : Over X)
        (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ SimplexCategory.mk n) →
          (T ⟶ (Scheme.Etale.forget X).obj (S.obj (op Δ)))),
        (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
          (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
          p Δ h θ ≫ (Scheme.Etale.forget X).map (S.map α.op) =
            p Δ' h' (α ≫ θ)) →
        ∃! f : T ⟶ (Scheme.Etale.forget X).obj M,
          ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
            f ≫ (Scheme.Etale.forget X).map (π Δ h θ) = p Δ h θ) ∧
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        μ ≫ π Δ h θ = S.map θ.op) ∧ Surjective μ.left := by
  rcases U with ⟨simp, N, inc, split, finite, M, π, hn, hu, μ, hμ, hc⟩
  dsimp at hU
  subst simp
  let top : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  refine ⟨M top, fun Δ h θ ↦ π top ⟨Δ, Nat.le_of_lt h⟩ h θ, μ top, ?_, ?_, ?_,
    hc top⟩
  · intro Δ Δ' h h' α θ
    exact hn top ⟨Δ, Nat.le_of_lt h⟩ ⟨Δ', Nat.le_of_lt h'⟩ h h'
      (SimplexCategory.Truncated.Hom.tr α _ _) θ
  · intro T p hp
    obtain ⟨f, hf, huniq⟩ := hu top T (fun Δ h θ ↦ p Δ.obj h θ) (by
      intro Δ Δ' h h' α θ
      exact hp Δ.obj Δ'.obj h h' α.hom θ)
    refine ⟨f, ?_, ?_⟩
    · intro Δ h θ
      exact hf ⟨Δ, Nat.le_of_lt h⟩ h θ
    · intro g hg
      apply huniq g
      intro Δ h θ
      exact hg Δ.obj h θ
  · intro Δ h θ
    exact hμ top ⟨Δ, Nat.le_of_lt h⟩ h θ

private theorem inclusion_congr
    {X : Scheme.{u}} {K : SimplicialObject X.Etale} {n : ℕ}
    (B C : FiniteSplitReplacementStage K n) (h : B = C) (q : Fin (n + 1)) :
    eqToHom (congrArg (fun A ↦ A.U.N q) h) ≫ C.U.inclusion q =
      B.U.inclusion q ≫ eqToHom (congrArg
        (fun A ↦ A.U.simplicial.obj
          (op ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩)) h) := by
  subst C
  simp

private theorem refinement_congr
    {X : Scheme.{u}} {K : SimplicialObject X.Etale} {n : ℕ}
    (B C : FiniteSplitReplacementStage K n) (h : B = C)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    eqToHom (congrArg (fun A ↦ A.U.simplicial.obj Δ) h) ≫ C.f.app Δ = B.f.app Δ := by
  subst C
  simp

/-- Compatible finite replacement stages give a finite split replacement.
Source: Stacks 0DAV, passage from compatible skeleta to a simplicial object.
Every object and every operator is read at a stage containing its degrees.
The compatibility equalities show that this value is independent of the stage;
all simplicial identities and the refinement naturality are checked at a common
finite stage. Splitting, finiteness and the matching universal property in a fixed
degree are the corresponding properties of that finite stage.
(auxiliary; not a blueprint node) -/
theorem exists_replacement_of_stage_tower
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (A : ∀ n, FiniteSplitReplacementStage K n)
    (e : ∀ n, (A (n + 1)).restrict n (Nat.le_succ n) = A n) :
    ∃ V : FiniteSplitEtaleHypercover X, Nonempty (V.simplicial ⟶ K) := by
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
    finite_each_degree := ?_ }, ⟨{ app := F, naturality := fun {Δ₁ Δ₂} p ↦ hnat Δ₁ Δ₂ p }⟩⟩
  intro n
  exact (A n).U.finite_each_degree ⟨n, Nat.lt_succ_self n⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
