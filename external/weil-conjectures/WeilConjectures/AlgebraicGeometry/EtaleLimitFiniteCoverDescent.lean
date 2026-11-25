/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteDiagramDescent
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage

/-! # Descent of a finite qcqs étale covering

Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YP. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend just the finite geometric covering, with its arrow equations.
Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YQ.
(blueprint: lem-weil-pbc-etale-limit-finite-cover-descent).

Proof: The limit base is qcqs by affine-limit permanence. The qcqs sources of the
étale structure maps give quasi-compact and quasi-separated structure maps, hence
finite presentation. Use 01ZM(1) to spread out U and each V_k. Each model is qcqs
because it is of finite presentation over a qcqs stage. Apply 07RP to its structure
map to make it étale. Choose a common upper bound of these finitely many stages,
retaining the isomorphisms to U and V_k by pullback composition. Use 01ZM(2) for
the arrows, and take another common upper bound; this gives the displayed arrow
identities with the same object isomorphisms. The finite disjoint union of the
arrows is locally finitely presented and has qcqs source and target. Its limit
base change is surjective because the original family covers. Apply 07RR to
make it surjective at one later stage. This is a covering at that stage. Every
subsequent family is its actual base change, hence is covering. All models
remain qcqs under these affine base changes. For empty K the union is the empty
scheme: 07RR makes the target empty at a stage, so the empty family covers.
No sheaves, nerve products, or complex maps are involved. -/
theorem exists_etale_limit_finite_cover_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
    ∃ (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k),
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
    (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
    (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
    (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) := by
  classical
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a ↦ inferInstance
  obtain ⟨i, Ui, Vi, fi, eU, eV, hUi, hVi, heq⟩ :=
    exists_etale_limit_finite_diagram_descent D c hc U K V f hV
  have : CompactSpace Ui.left := hUi.1
  have : QuasiSeparatedSpace Ui.left := hUi.2
  have (k : K) : CompactSpace (Vi k).left := (hVi k).1
  have (k : K) : QuasiSeparatedSpace (Vi k).left := (hVi k).2
  let F := Scheme.Etale.forget (D.obj (op i))
  let L := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i))
  have hcov : ∀ x : ((Over.pullback (c.π.app (op i))).obj (F.obj Ui)).left,
      ∃ k, ∃ y : ((Over.pullback (c.π.app (op i))).obj (F.obj (Vi k))).left,
        ((Over.pullback (c.π.app (op i))).map (F.map (fi k))).left y = x := by
    intro x
    have hx : eU.hom.left x ∈ ⋃ k, Set.range (f k).left := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hf
      rw [hf]
      trivial
    obtain ⟨k, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨k, (eV k).inv.left y, ?_⟩
    have h := congrArg (fun g ↦ g.left ((eV k).inv.left y)) (heq k)
    simp only [MorphismProperty.Comma.comp_left, Scheme.Hom.comp_apply] at h
    have hv : (eV k).hom.left ((eV k).inv.left y) = y := by
      change ((eV k).inv.left ≫ (eV k).hom.left) y = y
      simp [← MorphismProperty.Comma.comp_left]
    rw [hv, hy] at h
    have hu : Function.Injective eU.hom.left := by
      intro x y hxy
      have hh := congrArg eU.inv.left hxy
      simpa [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left] using hh
    exact hu h
  obtain ⟨j, a, hj⟩ := finite_family_joint_surjectivity_stage D c hc K (op i)
    (fun k ↦ F.obj (Vi k)) (F.obj Ui) (fun k ↦ F.map (fi k))
    (fun k ↦ by change LocallyOfFinitePresentation (Vi k).hom ∧
      QuasiCompact (Vi k).hom ∧ QuasiSeparated (Vi k).hom; exact ⟨inferInstance,
        @quasiCompact_of_compactSpace (Vi k).left (D.obj (op i)) (Vi k).hom
          (hVi k).1 (inferInstance : QuasiSeparatedSpace (D.obj (op i))),
        @QuasiSeparated.of_quasiSeparatedSpace _ _ (Vi k).hom (hVi k).2⟩)
    (by change LocallyOfFinitePresentation Ui.hom ∧ QuasiCompact Ui.hom ∧
        QuasiSeparated Ui.hom; exact ⟨inferInstance,
          @quasiCompact_of_compactSpace Ui.left (D.obj (op i)) Ui.hom
            hUi.1 (inferInstance : QuasiSeparatedSpace (D.obj (op i))),
          @QuasiSeparated.of_quasiSeparatedSpace _ _ Ui.hom hUi.2⟩)
    (fun k ↦ by change LocallyOfFinitePresentation (fi k).left; infer_instance) hcov
  let B := MorphismProperty.Over.pullback @Etale ⊤ (D.map a)
  let Lj := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j)
  let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (c.π.app j) (D.map a) (c.π.app (op i)) (c.w a).symm
  have hcover : Sieve.ofArrows (fun k ↦ B.obj (Vi k)) (fun k ↦ B.map (fi k)) ∈
      (D.obj j).smallEtaleTopology (B.obj Ui) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hs : ∀ x : ((Over.pullback (D.map a)).obj (F.obj Ui)).left,
        ∃ k, ∃ y : ((Over.pullback (D.map a)).obj (F.obj (Vi k))).left,
          ((Over.pullback (D.map a)).map (F.map (fi k))).left y = x := by
      have hh := hj j (𝟙 j)
      rw [Category.id_comp] at hh
      exact hh
    obtain ⟨k, y, hy⟩ := hs x
    refine Set.mem_iUnion.mpr ⟨k, y, ?_⟩
    change (((MorphismProperty.Over.pullback @Etale ⊤ (D.map a)).map (fi k)).left) y = x
    change (((MorphismProperty.Over.pullback @Etale ⊤ (D.map a)).map (fi k)).left) y = x at hy
    exact hy
  refine ⟨j.unop, B.obj Ui, (fun k ↦ B.obj (Vi k)), (fun k ↦ B.map (fi k)),
    (δ.app Ui).symm ≪≫ eU, (fun k ↦ (δ.app (Vi k)).symm ≪≫ eV k), ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · change CompactSpace ↥(pullback Ui.hom (D.map a)) ∧
      QuasiSeparatedSpace ↥(pullback Ui.hom (D.map a))
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _
      (pullback.fst Ui.hom (D.map a)) inferInstance hUi.1,
      @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst Ui.hom (D.map a))
        hUi.2 inferInstance⟩
  · intro k
    change CompactSpace ↥(pullback (Vi k).hom (D.map a)) ∧
      QuasiSeparatedSpace ↥(pullback (Vi k).hom (D.map a))
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _
      (pullback.fst (Vi k).hom (D.map a)) inferInstance (hVi k).1,
      @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (Vi k).hom (D.map a))
        (hVi k).2 inferInstance⟩
  · intro k
    change Lj.map (B.map (fi k)) ≫ (δ.app Ui).inv ≫ eU.hom =
      (δ.app (Vi k)).inv ≫ (eV k).hom ≫ f k
    have hn := δ.inv.naturality (fi k)
    change Lj.map (B.map (fi k)) ≫ (δ.app Ui).inv =
      (δ.app (Vi k)).inv ≫ L.map (fi k) at hn
    rw [← Category.assoc, hn, Category.assoc, heq k]
  · intro k
    have h := (D.map (homOfLE k.property).op).coverPreserving_etale.cover_preserve hcover
    simpa only [Sieve.functorPushforward_ofArrows, Scheme.Hom.Etale] using h


end AlgebraicGeometry.Etale
