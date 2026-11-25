/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import Mathlib.AlgebraicGeometry.LimitsOver

open CategoryTheory CategoryTheory.Limits Opposite
/-! Finite matching schemes for split replacement stages. The boundary-index
construction follows the proved construction in
`WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep`. -/

@[expose] public section
universe u v
namespace AlgebraicGeometry

private theorem sigma_qs {I : Type u} [Finite I] (T : I → Type u)
    [∀ i, TopologicalSpace (T i)] [∀ i, QuasiSeparatedSpace (T i)] :
    QuasiSeparatedSpace (Σ i, T i) := by
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

private theorem cofan_qcqs {X : Scheme.{u}} {I : Type} [Finite I]
    (W : I → X.Etale) (T : X.Etale) (ι : ∀ i, W i ⟶ T)
    (h : IsColimit (Cofan.mk T ι))
    (hc : ∀ i, CompactSpace (W i).left) (hq : ∀ i, QuasiSeparatedSpace (W i).left) :
    CompactSpace T.left ∧ QuasiSeparatedSpace T.left := by
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

private theorem stage_term_qcqs {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    CompactSpace (U.simplicial.obj Δ).left ∧
      QuasiSeparatedSpace (U.simplicial.obj Δ).left := by
  have hN (q : Fin (n + 1)) :
      CompactSpace (U.N q).left ∧ QuasiSeparatedSpace (U.N q).left := by
    obtain ⟨k, W, ι, ⟨h⟩, hf⟩ := U.finite_each_degree q
    exact cofan_qcqs W (U.N q) ι h (fun i ↦ (hf i).1) (fun i ↦ (hf i).2.1)
  let J := Σ q : Fin (n + 1),
    {α : Δ.unop.obj ⟶ SimplexCategory.mk q.val // Epi α}
  have : Finite J := by dsimp [J]; infer_instance
  exact cofan_qcqs (fun a : J ↦ U.N a.1) (U.simplicial.obj Δ)
    _ (U.splitting Δ) (fun a ↦ (hN a.1).1) (fun a ↦ (hN a.1).2)
end AlgebraicGeometry

namespace AlgebraicGeometry
open MorphismProperty
private abbrev QcEtale : MorphismProperty Scheme.{u} :=
  @Etale ⊓ (@QuasiCompact ⊓ @QuasiSeparated)

private instance : QcEtale.HasOfPostcompProperty QcEtale where
  of_postcomp f g hg hfg := by
    let : Etale g := hg.1
    let : QuasiSeparated g := hg.2.2
    let : Etale (f ≫ g) := hfg.1
    let : QuasiCompact (f ≫ g) := hfg.2.1
    let : QuasiSeparated (f ≫ g) := hfg.2.2
    exact ⟨Etale.of_comp f g, QuasiCompact.of_comp f g, QuasiSeparated.of_comp f g⟩

private def qcLift {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {n : ℕ} (U : TruncatedFiniteSplitEtaleHypercover X n) :
    SimplicialObject.Truncated (QcEtale.Over ⊤ X) n where
  obj Δ := MorphismProperty.Over.mk ⊤ (U.simplicial.obj Δ).hom (by
    have ht := stage_term_qcqs U Δ
    let := ht.1
    let := ht.2
    exact ⟨inferInstance,
      @quasiCompact_of_compactSpace _ X _ ht.1 inferInstance,
      @QuasiSeparated.of_quasiSeparatedSpace _ _ _ ht.2⟩)
  map f := MorphismProperty.Over.homMk (U.simplicial.map f).left
    (MorphismProperty.Over.w _) trivial
  map_id Δ := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) (U.simplicial.map_id Δ)
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) (U.simplicial.map_comp f g)

private abbrev BoundaryIndex (n : ℕ) :=
  CostructuredArrow (SimplexCategory.Truncated.inclusion n) (SimplexCategory.mk (n + 1))

private theorem boundaryIndex_finite (n : ℕ) : Finite (BoundaryIndex n) := by
  let f (a : BoundaryIndex n) :
      Σ r : Fin (n + 1), (SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :=
    ⟨⟨a.left.obj.len, Nat.lt_succ_of_le a.left.property⟩, a.hom⟩
  apply Finite.of_injective f
  rintro ⟨⟨a, ha⟩, ar, ah⟩ ⟨⟨b, hb⟩, br, bh⟩ h
  have hab : a = b := SimplexCategory.ext (congrArg (fun x ↦ x.1.val) h)
  subst b
  have hh : ah = bh := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst bh
  congr
  exact Subsingleton.elim _ _

@[instance_reducible] private noncomputable def boundaryIndex_finCategory (n : ℕ) :
    FinCategory (BoundaryIndex n) where
  fintypeObj := @Fintype.ofFinite _ (boundaryIndex_finite n)
  fintypeHom a b := by
    have : Finite (a.left.obj ⟶ b.left.obj) := inferInstance
    have : Finite (a ⟶ b) := Finite.of_injective (fun f ↦ f.left.hom) (by
      intro f g h
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      exact h)
    exact Fintype.ofFinite _

private def boundaryDiagram {D : Type*} [Category* D] {n : ℕ}
    (K : SimplicialObject.Truncated D n) : (BoundaryIndex n)ᵒᵖ ⥤ D :=
  (CostructuredArrow.proj _ _).op ⋙ K


/-- Source: Stacks Project, Hypercoverings, 0DAV; the finite matching limit.

Each nondegenerate object is a finite coproduct of qcqs schemes, hence qcqs.
The splitting cofans express every retained term as another finite coproduct,
so they too are qcqs. For this coproduct assertion, map its cofan to schemes
and use the homeomorphism with a finite topological disjoint union; compact
opens intersect compactly component by component.
The property etale, quasi-compact and quasi-separated is stable under composition,
base change and cancellation of postcomposition by itself. Therefore its over
category has finite limits and its forgetful functor to Over X preserves them.
Lift the truncated diagram to this category. The category of arrows from retained
simplices to [n+1] is finite; its opposite limit is the matching object. Its
projections give the displayed naturality. Apply preservation to get its limiting
cone in Over X, which gives existence and uniqueness for every test scheme over X.
The matching object's structure map is qcqs; since X is qcqs, its source is qcqs.
(auxiliary; not a blueprint node) -/
theorem exists_replacement_boundary {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) : Nonempty (ReplacementBoundary U) := by
  classical
  let := boundaryIndex_finCategory n
  let F := boundaryDiagram (qcLift U)
  let T := limit F
  let Forget := MorphismProperty.Over.forget QcEtale ⊤ X
  let c := Forget.mapCone (limit.cone F)
  let hc := isLimitOfPreserves Forget (limit.isLimit F)
  have et : Etale T.hom := T.prop.1
  let M : X.Etale := Scheme.Etale.mk T.hom
  let π (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) : M ⟶ U.simplicial.obj (op Δ) :=
    MorphismProperty.Over.homMk
      (limit.π F (op (CostructuredArrow.mk (Y := Δ) θ))).left
      (MorphismProperty.Over.w _) trivial
  refine ⟨⟨M, π, ?_, ?_, ?_, ?_⟩⟩
  · intro Δ Δ' α θ
    apply MorphismProperty.Over.Hom.ext
    have h := limit.w F (CostructuredArrow.homMk
      (f' := CostructuredArrow.mk (Y := Δ) θ)
      (f := CostructuredArrow.mk (Y := Δ') (α.hom ≫ θ)) α rfl).op
    exact congrArg (fun f ↦ f.left) h
  · intro Y p hp
    let s : Cone (F ⋙ Forget) := {
      pt := Y
      π := {
        app := fun a ↦ p a.unop.left a.unop.hom
        naturality := by
          intro a b f
          dsimp [F, boundaryDiagram]
          rw [Category.id_comp]
          have h := hp a.unop.left b.unop.left f.unop.left a.unop.hom
          have hw : f.unop.left.hom ≫ a.unop.hom = b.unop.hom :=
            CostructuredArrow.w f.unop
          rw [hw] at h
          exact h.symm } }
    refine ⟨hc.lift s, ?_, ?_⟩
    · intro Δ θ
      exact hc.fac s (op (CostructuredArrow.mk (Y := Δ) θ))
    · intro f hf
      apply hc.uniq s f
      intro a
      exact hf a.unop.left a.unop.hom
  · exact @QuasiCompact.compactSpace_of_compactSpace _ X T.hom T.prop.2.1
      inferInstance
  · exact @quasiSeparatedSpace_of_quasiSeparated _ X T.hom inferInstance T.prop.2.2
end AlgebraicGeometry
