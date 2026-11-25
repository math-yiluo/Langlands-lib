/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.LimitsOver
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! The initial finite cover in the split replacement construction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

private theorem zero_stage_of_cover
    {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    (T : X.Etale) (t : T ⟶ K.obj (op (SimplexCategory.mk 0)))
    (hsurj : Surjective T.hom)
    (hfinite : ∃ (k : ℕ) (V : Fin k → X.Etale) (ι : ∀ i, V i ⟶ T),
      Nonempty (IsColimit (Cofan.mk T ι)) ∧
        ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
          LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
            QuasiSeparated (V i).hom) :
    Nonempty (FiniteSplitReplacementStage K 0) := by
  classical
  let S : SimplicialObject.Truncated X.Etale 0 := (Functor.const _).obj T
  have hsplit (Δ : (SimplexCategory.Truncated 0)ᵒᵖ) :
      IsColimit (Cofan.mk (S.obj Δ)
        (fun a : Σ m : Fin 1,
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
          (𝟙 T) ≫ S.map (SimplexCategory.Truncated.Hom.tr a.2.val
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
    simplicial := S
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
      congr 2 }⟩⟩

/-- Source: Stacks Project, Hypercoverings, 01GJ and 094K, degree zero.

The degree-zero matching object of K is terminal over X. Thus its matching covering
map makes K_0 surjective over X. Its affine opens have open images covering X, so
compactness selects finitely many. Their disjoint union T is étale over X, and its
map to K_0 gives the degree-zero refinement. Take N_0=T, with identity inclusion;
the only surjection [0] to a retained degree is the identity, so this is a splitting.
The finite affine pieces give finite_each_degree and the map to the terminal matching
object is surjective. There are no nontrivial face or compatibility conditions in
this degree, and the unique maps of [0] give the constant truncated functor.
(auxiliary; not a blueprint node) -/
theorem exists_replacement_stage_zero
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K) :
    Nonempty (FiniteSplitReplacementStage K 0) := by
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
  let C : Scheme.Cover.{0} (Scheme.precoverage @Etale) X :=
    K₀.hom.cover (P := @Etale) inferInstance
  have : QuasiCompactCover C.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (C.f i).isOpenMap)
  obtain ⟨k, a, V, hV, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact C.toPreZeroHypercover
      (show IsCompact (⊤ : X.Opens).carrier from isCompact_univ)
  let W (i : Fin k) : X.Etale :=
    Scheme.Etale.mk ((hV i).fromSpec ≫ K₀.hom)
  let τ (i : Fin k) : W i ⟶ K₀ :=
    MorphismProperty.Over.homMk (hV i).fromSpec rfl trivial
  have : HasCoproductsOfShape (Fin k) X.Etale := by
    dsimp [Scheme.Etale]
    infer_instance
  let T := ∐ W
  have hT : Surjective T.hom := by
    constructor
    intro x
    have hx : x ∈ ⋃ i, C.f (a i) '' (V i : Set (C.X (a i))) := by
      rw [hcover]
      trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨i, y, hy, hxy⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z, (hV i).fromSpec z = y := by
      change y ∈ Set.range (hV i).fromSpec
      rw [(hV i).range_fromSpec]
      exact hy
    refine ⟨(Sigma.ι W i).left z, ?_⟩
    change ((Sigma.ι W i).left ≫ T.hom) z = x
    have hw : (Sigma.ι W i).left ≫ T.hom = (W i).hom :=
      MorphismProperty.Over.w (Sigma.ι W i)
    rw [hw]
    change K₀.hom ((hV i).fromSpec z) = x
    rw [hz]
    exact hxy
  apply zero_stage_of_cover K T (Sigma.desc τ) hT
  refine ⟨k, W, Sigma.ι W, ⟨coproductIsCoproduct W⟩, ?_⟩
  intro i
  let hc : CompactSpace (W i).left := by
    change CompactSpace (Spec Γ(C.X (a i), V i))
    infer_instance
  let hq : QuasiSeparatedSpace (W i).left := by
    change QuasiSeparatedSpace (Spec Γ(C.X (a i), V i))
    infer_instance
  refine ⟨hc, hq, inferInstance, ?_, ?_⟩
  · exact @quasiCompact_of_compactSpace _ X ((hV i).fromSpec ≫ K₀.hom)
      inferInstance inferInstance
  · change QuasiSeparated ((hV i).fromSpec ≫ K₀.hom)
    infer_instance

end AlgebraicGeometry.FiniteSplitEtaleHypercover
