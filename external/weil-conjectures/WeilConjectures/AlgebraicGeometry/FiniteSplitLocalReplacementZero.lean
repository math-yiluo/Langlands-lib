/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteEtaleSieveCover

/-! The constrained finite split replacement construction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

private theorem zero_stage_of_solving_cover
    {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    (T : X.Etale) (t : T ⟶ K.obj (op (SimplexCategory.mk 0)))
    (hsurj : Surjective T.hom)
    (hfinite : ∃ (k : ℕ) (V : Fin k → X.Etale) (ι : ∀ i, V i ⟶ T),
      Nonempty (IsColimit (Cofan.mk T ι)) ∧
        ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
          LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
            QuasiSeparated (V i).hom)
    (S : ∀ n : ℕ, Sieve (K.obj (op (SimplexCategory.mk n))))
    (hsolve : ∃ (l : ℕ) (W : Fin l → X.Etale) (ι : ∀ i, W i ⟶ T),
      Nonempty (IsColimit (Cofan.mk T ι)) ∧ ∀ i, S 0 (ι i ≫ t)) :
    ∃ A : FiniteSplitReplacementStage K 0, StageSolves K S A := by
  classical
  let Z : SimplicialObject.Truncated X.Etale 0 := (Functor.const _).obj T
  have hsplit (Δ : (SimplexCategory.Truncated 0)ᵒᵖ) :
      IsColimit (Cofan.mk (Z.obj Δ)
        (fun a : Σ m : Fin 1,
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
          (𝟙 T) ≫ Z.map (SimplexCategory.Truncated.Hom.tr a.2.val
            Δ.unop.property (Nat.le_of_lt_succ a.1.isLt)).op)) := by
    let J := Σ m : Fin 1, {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
    have hJ : Subsingleton J := by
      constructor
      rintro ⟨m, α⟩ ⟨l, β⟩
      have hl : l = m := Subsingleton.elim _ _
      subst l
      apply congrArg (Sigma.mk m)
      apply Subtype.ext
      have hm : m.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ m.isLt)
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      apply Fin.ext
      have ha := (α.val.toOrderHom i).isLt
      have hb := (β.val.toOrderHom i).isLt
      change (α.val.toOrderHom i).val < m.val + 1 at ha
      change (β.val.toOrderHom i).val < m.val + 1 at hb
      omega
    let j : J := ⟨⟨0, by decide⟩, SimplexCategory.const _ _ 0,
      SimplexCategory.epi_iff_surjective.mpr (by
        intro x
        exact ⟨0, Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)).symm⟩)⟩
    let _ : Unique J := { default := j, uniq := fun _ ↦ Subsingleton.elim _ _ }
    exact Cofan.isColimitMkOfUnique (Iso.refl T) J
  have empty (n : Fin 1) (l : ℕ) (h : l < n.val) : False := by omega
  let μ : T ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk T.hom (Category.comp_id _) trivial
  let U : TruncatedFiniteSplitEtaleHypercover X 0 := {
    simplicial := Z
    N := fun _ ↦ T
    inclusion := fun _ ↦ 𝟙 T
    splitting := hsplit
    finite_each_degree := fun _ ↦ hfinite
    matching := fun _ ↦ Scheme.Etale.mk (𝟙 X)
    projection := fun n Δ h _ ↦ (empty n _ h).elim
    projection_naturality := fun n Δ Δ' h h' α θ ↦ (empty n _ h).elim
    matching_universal := by
      intro n Y p hp
      refine ⟨Over.homMk Y.hom (Category.comp_id _), ?_, ?_⟩
      · intro Δ h θ
        exact (empty n _ h).elim
      · intro f hf
        exact Over.mkIdTerminal.hom_ext _ _
    matchingMap := fun _ ↦ μ
    matchingMap_projection := fun n Δ h θ ↦ (empty n _ h).elim
    matching_cover := fun _ ↦ hsurj }
  refine ⟨⟨U, {
    app := fun Δ ↦
      t ≫ K.map (SimplexCategory.const Δ.unop.obj (SimplexCategory.mk 0) 0).op
    naturality := by
      intro Δ₁ Δ₂ p
      change (𝟙 T) ≫ (t ≫ K.map _) = (t ≫ K.map _) ≫ K.map p.unop.hom.op
      simp only [Category.id_comp, Category.assoc, ← K.map_comp, ← op_comp]
      congr 2 }⟩, ?_⟩
  intro q
  have hq : q = 0 := Fin.ext (by omega)
  subst q
  obtain ⟨l, W, ι, hcol, hι⟩ := hsolve
  refine ⟨l, W, ι, hcol, ?_⟩
  intro i
  change S 0 (ι i ≫ (t ≫ K.map (SimplexCategory.const _ _ 0).op))
  rw [SimplexCategory.hom_zero_zero (SimplexCategory.const _ _ 0)]
  change S 0 (ι i ≫ (t ≫ K.map (𝟙 _)))
  simpa only [K.map_id, Category.comp_id] using hι i

/-- Source: Stacks, Hypercoverings, 01GJ and 094K, the initial covering step.

Proof: Pull the covering sieve S_0 back to the degree-zero covering object K_0.
Choose an etale covering family contained in S_0. Its images cover K_0 and then X.
Refine its members by affine opens. Since these etale images are open and X is
quasi-compact, finitely many suffice to cover X. Let T be their disjoint union.
The map T to K_0 defines the degree-zero refinement. The only degree-zero simplex
operator is the identity, so the constant truncated functor with nondegenerate
object T, identity inclusion, and terminal matching object is a split hypercover
stage. The chosen affine coproduct presentation proves StageSolves, by the sieve's
closure under precomposition. This also handles empty X and the empty covering.
(auxiliary; not a blueprint node) -/
theorem exists_local_replacement_stage_zero
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
    (S : ∀ n : ℕ, Sieve (K.obj (op (SimplexCategory.mk n))))
    (hS : S 0 ∈ X.smallEtaleTopology _) :
    ∃ A : FiniteSplitReplacementStage K 0, StageSolves K S A := by
  classical
  let K₀ := K.obj (op (SimplexCategory.mk 0))
  obtain ⟨M, π, μ, hn, hu, hp, hc⟩ := hK 0
  obtain ⟨s, hs, _⟩ := hu (Over.mk (𝟙 X))
    (fun Δ h θ ↦ (Nat.not_lt_zero _ h).elim)
    (by intro Δ Δ' h; exact (Nat.not_lt_zero _ h).elim)
  have hM : Surjective M.hom := by
    constructor
    intro x
    refine ⟨s.left x, ?_⟩
    change (s.left ≫ M.hom) x = x
    have hw : s.left ≫ M.hom = 𝟙 X := Over.w s
    exact congrArg (fun f : X ⟶ X ↦ f x) hw
  have hμ : Surjective μ.left := hc
  have hK₀ : Surjective K₀.hom := by
    have hh : Surjective (μ.left ≫ M.hom) := inferInstance
    have hw : μ.left ≫ M.hom = K₀.hom := MorphismProperty.Over.w μ
    rw [hw] at hh
    exact hh
  let M := Scheme.Etale.mk (𝟙 X)
  have : CompactSpace M.left := ‹CompactSpace X›
  let e : K₀ ⟶ M := MorphismProperty.Over.homMk K₀.hom (Category.comp_id _) trivial
  obtain ⟨T, t, k, W, ι, ht, hc, hW, hι⟩ :=
    exists_finite_etale_sieve_cover M K₀ e hK₀ (S 0) hS
  have hT : Surjective T.hom := by
    change Surjective (t.left ≫ K₀.hom) at ht
    rwa [MorphismProperty.Over.w t] at ht
  exact zero_stage_of_solving_cover K T t hT ⟨k, W, ι, hc, hW⟩ S
    ⟨k, W, ι, hc, hι⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
