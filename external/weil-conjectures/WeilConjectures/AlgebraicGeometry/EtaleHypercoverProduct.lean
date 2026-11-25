/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Products of étale hypercovers

Source: Stacks Project, Hypercoverings, Lemma 01GI (lemma-product-hypercoverings),
with the covering argument of Lemma 01GH (lemma-funny-gamma).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe uP

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The product in simplicial étale `X`-schemes is again a hypercover.
This product is computed termwise; products in `X.Etale` are scheme-theoretic fibre
products over `X`. Its projections `prod.fst U V` and `prod.snd U V` are natural
transformations, hence morphisms of augmented simplicial `X`-schemes.
Source: Stacks Project, Hypercoverings, Lemmas 01GI and 01GH.

Proof: (1) Fibre products in the small étale site exist. The termwise product has
induced faces and degeneracies; their identities and the naturality of its projections
follow from the universal property of fibre products [def-pc-fibre-product].
(2) By [lem-weil-pbc-matching-object-fibre-product], its matching scheme is the product
of the matching schemes, and its matching arrow is the product of their matching arrows.
At degree zero this is the augmentation to `X`.
(3) Factor that arrow as the product of the first matching arrow with the identity,
followed by the product of the identity with the second matching arrow. Each factor
is a base change of a surjective étale arrow, so is surjective étale by
[lem-weil-pbc-etale-covering-base-change].
(4) Apply [lem-weil-pbc-etale-covering-composition] to these two factors, then compose
with the matching-scheme isomorphism of step (2). This gives the covering condition
in every degree. The simplicial object and its two projections were supplied in step (1).
(auxiliary; not a blueprint node) -/
theorem isEtaleHypercover_prod (X : Scheme.{uP}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : SimplicialObject X.Etale) (hU : IsEtaleHypercover U)
    (hV : IsEtaleHypercover V) : IsEtaleHypercover (U ⨯ V) := by
  intro n
  obtain ⟨MU, πU, μU, hcU, hlU, hmU, hsU⟩ := hU n
  obtain ⟨MV, πV, μV, hcV, hlV, hmV, hsV⟩ := hV n
  let F := Scheme.Etale.forget X
  let p := prod.fst (X := U) (Y := V)
  let q := prod.snd (X := U) (Y := V)
  let hW (Δ : SimplexCategoryᵒᵖ) : IsLimit (BinaryFan.mk (p.app Δ) (q.app Δ)) :=
    isLimitOfHasBinaryProductOfPreservesLimit
      ((evaluation _ X.Etale).obj Δ) U V
  let hWF (Δ : SimplexCategoryᵒᵖ) :
      IsLimit (BinaryFan.mk (F.map (p.app Δ)) (F.map (q.app Δ))) :=
    mapIsLimitOfPreservesOfIsLimit F _ _ (hW Δ)
  let hM : IsLimit (BinaryFan.mk (F.map (prod.fst : MU ⨯ MV ⟶ MU))
      (F.map (prod.snd : MU ⨯ MV ⟶ MV))) := isLimitOfHasBinaryProductOfPreservesLimit F MU MV
  let π (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n) :
      MU ⨯ MV ⟶ (U ⨯ V).obj (Opposite.op Δ) :=
    BinaryFan.IsLimit.lift (hW (Opposite.op Δ)) (prod.fst ≫ πU Δ h θ) (prod.snd ≫ πV Δ h θ)
  have hπp (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n) :
      π Δ h θ ≫ p.app (Opposite.op Δ) = prod.fst ≫ πU Δ h θ :=
    BinaryFan.IsLimit.lift_fst (hW (Opposite.op Δ)) _ _
  have hπq (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n) :
      π Δ h θ ≫ q.app (Opposite.op Δ) = prod.snd ≫ πV Δ h θ :=
    BinaryFan.IsLimit.lift_snd (hW (Opposite.op Δ)) _ _
  let μ : (U ⨯ V).obj (Opposite.op (SimplexCategory.mk n)) ⟶ MU ⨯ MV :=
    prod.lift (p.app _ ≫ μU) (q.app _ ≫ μV)
  refine ⟨MU ⨯ MV, π, μ, ?_, ?_, ?_, ?_⟩
  · intro Δ Δ' h h' α θ
    apply BinaryFan.IsLimit.hom_ext (hW (Opposite.op Δ'))
    · change (π Δ h θ ≫ (U ⨯ V).map α.op) ≫ p.app _ = π Δ' h' (α ≫ θ) ≫ p.app _
      rw [Category.assoc, p.naturality, ← Category.assoc, hπp, hπp, Category.assoc, hcU]
    · change (π Δ h θ ≫ (U ⨯ V).map α.op) ≫ q.app _ = π Δ' h' (α ≫ θ) ≫ q.app _
      rw [Category.assoc, q.naturality, ← Category.assoc, hπq, hπq, Category.assoc, hcV]
  · intro T c hc
    obtain ⟨fU, hfU, huU⟩ := hlU T
      (fun Δ h θ ↦ c Δ h θ ≫ F.map (p.app _)) (by
        intro Δ Δ' h h' α θ
        rw [Category.assoc, ← F.map_comp, ← p.naturality, F.map_comp, ← Category.assoc, hc])
    obtain ⟨fV, hfV, huV⟩ := hlV T
      (fun Δ h θ ↦ c Δ h θ ≫ F.map (q.app _)) (by
        intro Δ Δ' h h' α θ
        rw [Category.assoc, ← F.map_comp, ← q.naturality, F.map_comp, ← Category.assoc, hc])
    refine ⟨BinaryFan.IsLimit.lift hM fU fV, ?_, ?_⟩
    · intro Δ h θ
      apply BinaryFan.IsLimit.hom_ext (hWF (Opposite.op Δ))
      · change (_ ≫ F.map (π Δ h θ)) ≫ F.map (p.app _) =
          c Δ h θ ≫ F.map (p.app _)
        rw [Category.assoc, ← F.map_comp, hπp, F.map_comp, ← Category.assoc]
        exact (congrArg (fun k ↦ k ≫ F.map (πU Δ h θ))
          (show BinaryFan.IsLimit.lift hM fU fV ≫ F.map prod.fst = fU from
            BinaryFan.IsLimit.lift_fst hM fU fV)).trans (hfU Δ h θ)
      · change (_ ≫ F.map (π Δ h θ)) ≫ F.map (q.app _) =
          c Δ h θ ≫ F.map (q.app _)
        rw [Category.assoc, ← F.map_comp, hπq, F.map_comp, ← Category.assoc]
        exact (congrArg (fun k ↦ k ≫ F.map (πV Δ h θ))
          (show BinaryFan.IsLimit.lift hM fU fV ≫ F.map prod.snd = fV from
            BinaryFan.IsLimit.lift_snd hM fU fV)).trans (hfV Δ h θ)
    · intro g hg
      apply BinaryFan.IsLimit.hom_ext hM
      · change g ≫ F.map prod.fst = _
        rw [BinaryFan.IsLimit.lift_fst hM]
        apply huU
        intro Δ h θ
        rw [Category.assoc, ← F.map_comp, ← hπp, F.map_comp, ← Category.assoc, hg]
      · change g ≫ F.map prod.snd = _
        rw [BinaryFan.IsLimit.lift_snd hM]
        apply huV
        intro Δ h θ
        rw [Category.assoc, ← F.map_comp, ← hπq, F.map_comp, ← Category.assoc, hg]
  · intro Δ h θ
    apply BinaryFan.IsLimit.hom_ext (hW (Opposite.op Δ))
    · change (μ ≫ π Δ h θ) ≫ p.app _ = (U ⨯ V).map θ.op ≫ p.app _
      rw [Category.assoc, hπp, ← Category.assoc]
      dsimp [μ]
      rw [prod.lift_fst, Category.assoc, hmU, p.naturality]
    · change (μ ≫ π Δ h θ) ≫ q.app _ = (U ⨯ V).map θ.op ≫ q.app _
      rw [Category.assoc, hπq, ← Category.assoc]
      dsimp [μ]
      rw [prod.lift_snd, Category.assoc, hmV, q.naturality]
  · let d := Opposite.op (SimplexCategory.mk n)
    let eW := (Over.isPullback_of_binaryFan_isLimit _ (hWF d)).isoPullback
    let eM := (Over.isPullback_of_binaryFan_isLimit _ hM).isoPullback
    let f := pullback.map (U.obj d).hom (V.obj d).hom MU.hom MV.hom
      μU.left μV.left (𝟙 X)
      ((Category.comp_id _).trans μU.w.symm) ((Category.comp_id _).trans μV.w.symm)
    have hf : Surjective f := MorphismProperty.pullbackMap hsU hsV μU.w.symm μV.w.symm
    have heMfst : eM.hom ≫ pullback.fst MU.hom MV.hom =
        (prod.fst : MU ⨯ MV ⟶ MU).left := IsPullback.isoPullback_hom_fst _
    have heMsnd : eM.hom ≫ pullback.snd MU.hom MV.hom =
        (prod.snd : MU ⨯ MV ⟶ MV).left := IsPullback.isoPullback_hom_snd _
    have heWfst : eW.hom ≫ pullback.fst (U.obj d).hom (V.obj d).hom =
        (p.app d).left := IsPullback.isoPullback_hom_fst _
    have heWsnd : eW.hom ≫ pullback.snd (U.obj d).hom (V.obj d).hom =
        (q.app d).left := IsPullback.isoPullback_hom_snd _
    have hffst : f ≫ pullback.fst MU.hom MV.hom =
        pullback.fst (U.obj d).hom (V.obj d).hom ≫ μU.left := pullback.lift_fst _ _ _
    have hfsnd : f ≫ pullback.snd MU.hom MV.hom =
        pullback.snd (U.obj d).hom (V.obj d).hom ≫ μV.left := pullback.lift_snd _ _ _
    have he : μ.left ≫ eM.hom = eW.hom ≫ f := by
      apply pullback.hom_ext
      · change (μ.left ≫ eM.hom) ≫ pullback.fst MU.hom MV.hom =
          (eW.hom ≫ f) ≫ pullback.fst MU.hom MV.hom
        rw [Category.assoc, Category.assoc, heMfst, hffst, ← Category.assoc, heWfst]
        change (μ ≫ prod.fst).left = (p.app d ≫ μU).left
        exact congrArg (fun k : (U ⨯ V).obj d ⟶ MU ↦ k.left)
          (prod.lift_fst (p.app d ≫ μU) (q.app d ≫ μV))
      · change (μ.left ≫ eM.hom) ≫ pullback.snd MU.hom MV.hom =
          (eW.hom ≫ f) ≫ pullback.snd MU.hom MV.hom
        rw [Category.assoc, Category.assoc, heMsnd, hfsnd, ← Category.assoc, heWsnd]
        change (μ ≫ prod.snd).left = (q.app d ≫ μV).left
        exact congrArg (fun k : (U ⨯ V).obj d ⟶ MV ↦ k.left)
          (prod.lift_snd (p.app d ≫ μU) (q.app d ≫ μV))
    have hμ : μ.left = eW.hom ≫ f ≫ eM.inv := by
      rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hμ]
    infer_instance

end AlgebraicGeometry
