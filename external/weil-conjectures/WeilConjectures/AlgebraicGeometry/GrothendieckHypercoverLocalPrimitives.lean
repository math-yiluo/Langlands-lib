/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalEpimorphism
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement
import Mathlib.AlgebraicGeometry.LimitsOver
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-! # Detection by local primitives on finite hypercover refinements

Source: Stacks Project, Hypercoverings, Tag 01H0, the finite local lifting step.
The image-family formulation for arbitrary Grothendieck coefficients is an
explicit generalization of that argument for abelian sheaves.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

section Geometry
variable {A}

private theorem hypercover_term_qcqs (U : FiniteSplitEtaleHypercover X) (n : ℕ) :
    CompactSpace (U.simplicial.obj (op (SimplexCategory.mk n))).left ∧
      QuasiSeparatedSpace (U.simplicial.obj (op (SimplexCategory.mk n))).left := by
  have sigma_qs : ∀ {I : Type u} [Finite I] (T : I → Type u)
      [∀ i, TopologicalSpace (T i)] [∀ i, QuasiSeparatedSpace (T i)],
      QuasiSeparatedSpace (Σ i, T i) := by
    intro I _ T _ _
    constructor
    intro U V hU hUc hV hVc
    have he : U ∩ V = ⋃ i, Sigma.mk i ''
        ((Sigma.mk i ⁻¹' U) ∩ (Sigma.mk i ⁻¹' V)) := by
      ext ⟨i, x⟩
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
      constructor
      · intro h; exact ⟨i, x, h, rfl⟩
      · rintro ⟨j, y, h, he⟩; cases he; exact h
    rw [he]
    apply isCompact_iUnion
    intro i
    apply IsCompact.image _ continuous_sigmaMk
    apply IsCompact.inter_of_isOpen
    · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc
    · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hVc
    · exact hU.preimage continuous_sigmaMk
    · exact hV.preimage continuous_sigmaMk
  have cofan_qcqs : ∀ {I : Type} [Finite I] (W : I → X.Etale) (T : X.Etale),
      (ι : ∀ i, W i ⟶ T) → IsColimit (Cofan.mk T ι) →
      (∀ i, CompactSpace (W i).left) → (∀ i, QuasiSeparatedSpace (W i).left) →
      CompactSpace T.left ∧ QuasiSeparatedSpace T.left := by
    intro I _ W T ι h hc hq
    let F := Scheme.Etale.forget X ⋙ Over.forget X
    have : PreservesColimitsOfShape (Discrete I) F := by
      have : PreservesColimitsOfShape (Discrete I)
          (MorphismProperty.Over.forget (@Etale : MorphismProperty Scheme) ⊤ X) :=
        inferInstance
      dsimp [F, Scheme.Etale.forget]
      infer_instance
    let c := Cofan.mk T ι
    let h' := Cofan.isColimitMapCoconeEquiv F W c (isColimitOfPreserves F h)
    let e : T.left ≅ ∐ (fun i ↦ (W i).left) :=
      h'.coconePointUniqueUpToIso (coproductIsCoproduct _)
    let e' : (∐ fun i ↦ (W i).left) ≅
        ∐ (fun i : ULift.{u} I ↦ (W i.down).left) :=
      Sigma.whiskerEquiv (f := fun i : I ↦ (W i).left)
        (g := fun i : ULift.{u} I ↦ (W i.down).left) Equiv.ulift.symm
        (fun _ ↦ Iso.refl _)
    let eh := Scheme.Hom.homeomorph (e ≪≫ e').hom
    let hc' (i : ULift.{u} I) : CompactSpace (W i.down).left := hc i.down
    let hq' (i : ULift.{u} I) : QuasiSeparatedSpace (W i.down).left := hq i.down
    have hs := sigma_qs (fun i : ULift.{u} I ↦ (W i.down).left)
    have hh := sigmaMk (fun i : ULift.{u} I ↦ (W i.down).left)
    exact ⟨(eh.trans hh.symm).symm.compactSpace, (quasiSeparatedSpace_congr
      (eh.trans hh.symm)).mpr hs⟩
  have hN (q : ℕ) : CompactSpace (U.splitting.N q).left ∧
      QuasiSeparatedSpace (U.splitting.N q).left := by
    obtain ⟨k, W, ι, ⟨h⟩, hf⟩ := U.finite_each_degree q
    exact cofan_qcqs W (U.splitting.N q) ι h (fun i ↦ (hf i).1) (fun i ↦ (hf i).2.1)
  exact cofan_qcqs _ _ _ (U.splitting.isColimit (op (SimplexCategory.mk n)))
    (fun a ↦ (hN a.1.unop.len).1) (fun a ↦ (hN a.1.unop.len).2)

omit [Abelian A] [IsGrothendieckAbelian A] in
private theorem glue_coproduct_sections {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology A) (B : A)
    {l : ℕ} (T : Fin l → X.Etale) (V : X.Etale) (ι : ∀ i, T i ⟶ V)
    (hc : IsColimit (Cofan.mk V ι)) (s : ∀ i, B ⟶ F.obj.obj (op (T i))) :
    ∃! t : B ⟶ F.obj.obj (op V), ∀ i, t ≫ F.obj.map (ι i).op = s i := by
  classical
  let W₀ : Scheme.{u} := ∐ fun i ↦ (T i).left
  let f : W₀ ⟶ X := Sigma.desc (fun i ↦ (T i).hom)
  let : Etale f := IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (T i).prop)
  let W : X.Etale := Scheme.Etale.mk f
  let κ : ∀ i, T i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (T i).left) i)
      (by dsimp [W]; simp [f])
  have hW : IsColimit (Cofan.mk W κ) := by
    refine Cofan.IsColimit.mk _ (fun t ↦
      MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (t.inj i).left)) ?_) ?_ ?_
    · change Sigma.desc (fun i ↦ (t.inj i).left) ≫ t.pt.hom = f
      apply Sigma.hom_ext
      intro i
      simp [f, ← Category.assoc]
    · intro t i
      apply MorphismProperty.Over.Hom.ext
      exact Sigma.ι_comp_desc _ _
    · intro t m hm
      apply MorphismProperty.Over.Hom.ext
      apply Sigma.hom_ext
      intro i
      have h := congrArg (fun z ↦ z.left) (hm i)
      change Sigma.ι (fun i ↦ (T i).left) i ≫ m.left = (t.inj i).left at h
      simpa using h
  let e : W ≅ V := hW.coconePointUniqueUpToIso hc
  have he (i : Fin l) : κ i ≫ e.hom = ι i :=
    hW.comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hκ : Sieve.ofArrows T κ ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff κ).mpr
    exact (sigmaOpenCover (fun i ↦ (T i).left)).iUnion_range
  have hv {Z : X.Etale} {i j : Fin l} (a : Z ⟶ T i) (b : Z ⟶ T j)
      (h : a ≫ κ i = b ≫ κ j) : s i ≫ F.obj.map a.op = s j ≫ F.obj.map b.op := by
    by_cases hij : i = j
    · subst j
      have hab : a = b := by
        apply MorphismProperty.Over.Hom.ext
        exact (cancel_mono (Sigma.ι (fun i ↦ (T i).left) i)).mp
          (congrArg (fun z ↦ z.left) h)
      rw [hab]
    · have : IsEmpty Z.left :=
        isEmpty_of_commSq_sigmaι_of_ne
          (g := fun i ↦ (T i).left) ⟨congrArg (fun z ↦ z.left) h⟩ hij
      exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F Z).hom_ext _ _
  let t := F.property.amalgamateOfArrows κ hκ s (@hv)
  refine ⟨t ≫ F.obj.map e.inv.op, ?_, ?_⟩
  · intro i
    have hei : ι i ≫ e.inv = κ i := by rw [← he i]; simp
    rw [Category.assoc, ← F.obj.map_comp, ← op_comp, hei]
    exact F.property.amalgamateOfArrows_map κ hκ s (@hv) i
  · intro t' ht'
    have htt : t' ≫ F.obj.map e.hom.op = t := by
      apply F.property.hom_ext_ofArrows κ hκ
      intro i
      rw [Category.assoc, ← F.obj.map_comp, ← op_comp, he i, ht' i]
      exact (F.property.amalgamateOfArrows_map κ hκ s (@hv) i).symm
    apply (cancel_mono (F.obj.map e.hom.op)).mp
    rw [htt]
    simp only [Category.assoc, ← F.obj.map_comp, ← op_comp, Iso.hom_inv_id,
      op_id]
    rw [F.obj.map_id, Category.comp_id]


private def LocalEpiDetection : Prop :=
  ∀ {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T),
    (∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) → g = 0

set_option backward.isDefEq.respectTransparency false in
private theorem local_primitives_of_local_epi
    (hdet : LocalEpiDetection (X := X) (A := A))
    (S : ShortComplex (Sheaf X.smallEtaleTopology A)) (hS : S.Exact)
    (U : FiniteSplitEtaleHypercover X) (n : ℕ) (B T : A)
    (x : B ⟶ S.X₂.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk n)))))
    (hx : x ≫ S.g.hom.app _ = 0) (g : B ⟶ T)
    (hkill : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (B' : A)
      (π : B' ⟶ B)
      (l : B' ⟶ S.X₁.obj.obj (op (V.simplicial.obj (op (SimplexCategory.mk n))))),
      l ≫ S.f.hom.app _ = π ≫ x ≫ S.X₂.obj.map
        (f.app (op (SimplexCategory.mk n))).op → π ≫ g = 0) :
    g = 0 := by
  classical
  let W := U.simplicial.obj (op (SimplexCategory.mk n))
  have hW := hypercover_term_qcqs U n
  have : CompactSpace W.left := hW.1
  have : QuasiSeparatedSpace W.left := hW.2
  let ev : Sheaf X.smallEtaleTopology A ⥤ A :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W)
  let z : B ⟶ ev.obj (kernel S.g) :=
    kernel.lift (ev.map S.g) x hx ≫ (PreservesKernel.iso ev S.g).inv
  have hz : z ≫ ev.map (kernel.ι S.g) = x := by
    simp only [z, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := hS.epi_kernelLift
  apply hdet p W B T z g
  intro B' π R hR hlifts
  obtain ⟨V, f, hf⟩ := exists_refinement_solving_local_requirements U n 1
    (fun _ ↦ ⟨n, by omega⟩) (fun _ ↦ R) (fun _ ↦ hR)
  obtain ⟨k, Z, ι, ⟨hc⟩, hs⟩ := hf ⟨n, by omega⟩
  have hr (i : Fin k) : R (ι i ≫ f.app (op (SimplexCategory.mk n))) := by
    simpa using hs 0 rfl i
  choose l hl using fun i ↦ hlifts (Z i) (ι i ≫ f.app (op (SimplexCategory.mk n))) (hr i)
  obtain ⟨a, ha, -⟩ := glue_coproduct_sections S.X₁ B' Z _ ι hc l
  let K := kernel S.g
  let b := π ≫ z ≫ K.obj.map (f.app (op (SimplexCategory.mk n))).op
  have hab (i : Fin k) :
      (a ≫ p.hom.app _) ≫ K.obj.map (ι i).op = b ≫ K.obj.map (ι i).op := by
    rw [Category.assoc, ← p.hom.naturality, ← Category.assoc, ha i, hl i]
    simp only [b, K, op_comp, Functor.map_comp, Category.assoc]
  obtain ⟨c, _, hc'⟩ := glue_coproduct_sections K B' Z _ ι hc
    (fun i ↦ b ≫ K.obj.map (ι i).op)
  have hp : a ≫ p.hom.app _ = b :=
    (hc' _ hab).trans (hc' _ (fun _ ↦ rfl)).symm
  apply hkill V f B' π a
  have h := congrArg (fun v ↦ v ≫ (kernel.ι S.g).hom.app
    (op (V.simplicial.obj (op (SimplexCategory.mk n))))) hp
  rw [Category.assoc] at h
  change a ≫ (p ≫ kernel.ι S.g).hom.app _ = _ at h
  rw [kernel.lift_ι] at h
  calc
    _ = b ≫ (kernel.ι S.g).hom.app _ := h
    _ = _ := by
      dsimp only [b]
      rw [Category.assoc, Category.assoc, (kernel.ι S.g).hom.naturality,
        ← Category.assoc z]
      change π ≫ (z ≫ ev.map (kernel.ι S.g)) ≫ _ = _
      rw [hz]

end Geometry

/-- Local primitives after refinement jointly detect a morphism from the source.
Source: Stacks Project, Hypercoverings, Tag 01H0, first proof, local killing of
vertical cohomology classes; finite split refinement construction.
(auxiliary; not a blueprint node).

Proof: evaluation preserves kernels, so x factors through the sections of
K = ker(S.g). Exactness makes the canonical map p : S.X₁ → K epic. The terms of
U are qcqs: each nondegenerate summand is a finite coproduct of the qcqs pieces
in finite_each_degree, and the split decomposition is a finite coproduct of
these summands. Apply eq_zero_of_locally_liftable_maps to p at the degree-n term.
For any source map π and covering sieve R on which πx lifts, use
exists_refinement_solving_local_requirements with the single requirement R
in degree n. It supplies V → U and a finite colimiting cofan in V_n such that
each composite to U_n belongs to R. Choose a primitive on each cofan piece.

An A-valued sheaf glues morphisms from an arbitrary fixed source over this
cofan. To verify this directly, identify the cofan with the scheme coproduct.
Its inclusions form an etale cover. Maps to two distinct summands have empty
source, where the sheaf has terminal sections; maps to the same summand agree
by monicity. Thus arbitrary morphisms to the section objects on the pieces
are compatible and glue uniquely. This includes the empty cofan.

Glue the chosen primitives to l on V_n. Naturality of p and uniqueness of the
gluing imply that p(l) is the restriction of πx, now regarded in K. Composing
with K → S.X₂ and using its naturality gives exactly the displayed primitive
equation. The assumed hkill gives πg = 0 for each such source. The local
epimorphism detector concludes g = 0. No global projectivity or element
presentation of the coefficient category is used. -/
theorem eq_zero_of_refinement_primitives
    (S : ShortComplex (Sheaf X.smallEtaleTopology A)) (hS : S.Exact)
    (U : FiniteSplitEtaleHypercover X) (n : ℕ) (B T : A)
    (x : B ⟶ S.X₂.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk n)))))
    (hx : x ≫ S.g.hom.app _ = 0) (g : B ⟶ T)
    (hkill : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (B' : A)
      (π : B' ⟶ B)
      (l : B' ⟶ S.X₁.obj.obj (op (V.simplicial.obj (op (SimplexCategory.mk n))))),
      l ≫ S.f.hom.app _ = π ≫ x ≫ S.X₂.obj.map
        (f.app (op (SimplexCategory.mk n))).op → π ≫ g = 0) :
    g = 0 := by
  exact local_primitives_of_local_epi (eq_zero_of_locally_liftable_maps A)
    S hS U n B T x hx g hkill

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
