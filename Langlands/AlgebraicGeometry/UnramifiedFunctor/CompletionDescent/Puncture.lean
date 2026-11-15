import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Points
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Comparison over an open subset of the base

Let `π : S' ⟶ S`, let `U` be an open subset of `S` and `U' = π⁻¹(U)`. Let `q' : X' ⟶ S'`
represent the base change of a presheaf `F` along `π` and `q_U : X_U ⟶ U` represent its
base change along `U ⟶ S`. The part `P' = X' ×_{S'} U'` of `X'` over `U'` maps to `X_U` by
the morphism `puncMap` classifying the universal element of `X'`. This file proves that the
two elements of `F` that a morphism into `P'` defines agree, and that `puncMap` is affine
when `π` is: `P'` is the base change of `X_U` along `U' ⟶ U`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

variable {S S' : Scheme.{u}} (π : S' ⟶ S) {F : (Over S)ᵒᵖ ⥤ Type v} (U : S.Opens)
  {X' : Scheme.{u}} {q' : X' ⟶ S'} (e' : (baseChange π F).RepresentableBy (Over.mk q'))
  {XU : Scheme.{u}} {qU : XU ⟶ U} (eU : (baseChange U.ι F).RepresentableBy (Over.mk qU))

/-- The part of `X'` over `U' = π⁻¹(U)`. -/
abbrev puncSource (q' : X' ⟶ S') : Scheme.{u} := pullback q' (π ⁻¹ᵁ U).ι

/-- The open immersion of the part of `X'` over `U'` into `X'`. -/
abbrev puncι (q' : X' ⟶ S') : puncSource π U q' ⟶ X' := pullback.fst _ _

/-- The structure morphism `P' ⟶ U' ⟶ U`. -/
def puncBase (q' : X' ⟶ S') : puncSource π U q' ⟶ U := pullback.snd _ _ ≫ π ∣_ U

lemma puncBase_ι (q' : X' ⟶ S') :
    puncBase π U q' ≫ U.ι = puncι π U q' ≫ q' ≫ π := by
  rw [puncBase, Category.assoc, morphismRestrict_ι, ← Category.assoc, ← pullback.condition,
    Category.assoc]

/-- The morphism `P' ⟶ X_U` classifying the universal element of `X'` restricted to `P'`. -/
def puncMap : puncSource π U q' ⟶ XU :=
  (eU.homEquiv.symm (pt e' ((Over.map U.ι).obj (Over.mk (puncBase π U q'))) (puncι π U q')
    (puncBase_ι π U q').symm)).left

lemma puncMap_comp : puncMap π U e' eU ≫ qU = puncBase π U q' :=
  Over.w (eU.homEquiv.symm _)

/-- The two elements of `F(T)` defined by a morphism `a : T ⟶ P'` coincide: the one given by
`a ≫ puncMap` through `X_U` and the one given by `a` through `X'`. -/
lemma pt_puncMap (T : Over S) (a : T.left ⟶ puncSource π U q')
    (ha : a ≫ puncι π U q' ≫ q' ≫ π = T.hom) :
    pt eU T (a ≫ puncMap π U e' eU) (by
      rw [Category.assoc, reassoc_of% puncMap_comp, puncBase_ι, ha]) =
      pt e' T (a ≫ puncι π U q') (by rw [Category.assoc, ha]) := by
  let T₀ : Over S := (Over.map U.ι).obj (Over.mk (puncBase π U q'))
  let f : T ⟶ T₀ := Over.homMk a (by
    simp only [T₀, Over.map_obj_hom, Over.mk_hom]
    rw [puncBase_ι, ha])
  let h : Over.mk (puncBase π U q') ⟶ Over.mk qU :=
    eU.homEquiv.symm (pt e' T₀ (puncι π U q') (puncBase_ι π U q').symm)
  have hh : h.left ≫ qU ≫ U.ι = T₀.hom := by
    rw [← Category.assoc]
    exact congrArg (· ≫ U.ι) (Over.w h)
  have k : pt eU T₀ h.left hh = pt e' T₀ (puncι π U q') (puncBase_ι π U q').symm :=
    (homEquiv_eq_pt eU h).symm.trans (eU.homEquiv.apply_symm_apply _)
  exact (pt_comp eU f h.left hh).symm.trans ((congrArg (F.map f.op) k).trans
    (pt_comp e' f (puncι π U q') (puncBase_ι π U q').symm))

/-- Two morphisms into `P'` with the same composite to `U` and the same element of `F` through
`X'` have the same composite with `puncMap`. -/
lemma puncMap_eq_of_pt_eq {T : Over S} {a b : T.left ⟶ puncSource π U q'}
    (ha : a ≫ puncι π U q' ≫ q' ≫ π = T.hom) (hb : b ≫ puncι π U q' ≫ q' ≫ π = T.hom)
    (h : pt e' T (a ≫ puncι π U q') (by rw [Category.assoc, ha]) =
      pt e' T (b ≫ puncι π U q') (by rw [Category.assoc, hb])) :
    a ≫ puncMap π U e' eU = b ≫ puncMap π U e' eU := by
  have hU : (a ≫ puncMap π U e' eU) ≫ qU = (b ≫ puncMap π U e' eU) ≫ qU := by
    rw [Category.assoc, Category.assoc, puncMap_comp, ← cancel_mono U.ι, Category.assoc,
      Category.assoc, puncBase_ι, ha, hb]
  refine pt_inj eU ?_ ?_ hU ?_
  · rw [Category.assoc, reassoc_of% puncMap_comp, puncBase_ι, ha]
  · rw [Category.assoc, reassoc_of% puncMap_comp, puncBase_ι, hb]
  · rw [pt_puncMap π U e' eU T a ha, pt_puncMap π U e' eU T b hb]
    exact h

/-- The canonical morphism from `P'` to the base change `X_U ×_U U'`. -/
def puncComparison : puncSource π U q' ⟶ pullback qU (π ∣_ U) :=
  pullback.lift (puncMap π U e' eU) (pullback.snd _ _) (by rw [puncMap_comp]; rfl)

/-- The base change `X_U ×_U U'` as an object over `S`. -/
abbrev puncTarget (qU : XU ⟶ U) : Over S :=
  Over.mk (pullback.snd qU (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι ≫ π)

lemma pullback_fst_comp (qU : XU ⟶ U) :
    pullback.fst qU (π ∣_ U) ≫ qU ≫ U.ι = (puncTarget π U qU).hom := by
  show _ = pullback.snd qU (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι ≫ π
  rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition,
    Category.assoc]

/-- The inverse of `puncComparison`, as a morphism to `X'`. -/
lemma exists_puncInv :
    ∃ (a : pullback qU (π ∣_ U) ⟶ X') (hac : a ≫ q' = pullback.snd _ _ ≫ (π ⁻¹ᵁ U).ι),
      pt e' (puncTarget π U qU) a (by rw [← Category.assoc, hac, Category.assoc]; rfl) =
        pt eU (puncTarget π U qU) (pullback.fst _ _) (pullback_fst_comp π U qU) :=
  exists_pt e' (puncTarget π U qU) (pullback.snd _ _ ≫ (π ⁻¹ᵁ U).ι)
    (by rw [Category.assoc]; rfl) _

/-- The part of `X'` over `U'` is the base change of `X_U` along `U' ⟶ U`. -/
theorem isIso_puncComparison : IsIso (puncComparison π U e' eU) := by
  obtain ⟨a, hac, hpt⟩ := exists_puncInv π U e' eU
  let ψ : pullback qU (π ∣_ U) ⟶ puncSource π U q' := pullback.lift a (pullback.snd _ _) hac
  have hψj : ψ ≫ puncι π U q' = a := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd q' (π ⁻¹ᵁ U).ι = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hψ : ψ ≫ puncι π U q' ≫ q' ≫ π = (puncTarget π U qU).hom := by
    rw [reassoc_of% hψj, reassoc_of% hac]
    rfl
  let c := puncComparison π U e' eU
  have hc₁ : c ≫ pullback.fst qU (π ∣_ U) = puncMap π U e' eU := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd qU (π ∣_ U) = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨ψ, ?_, ?_⟩
  · -- `puncComparison ≫ ψ = 𝟙`
    let T : Over S := Over.mk (puncι π U q' ≫ q' ≫ π)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hψj]
      have hq : (c ≫ a) ≫ q' = puncι π U q' ≫ q' := by
        rw [Category.assoc, hac, reassoc_of% hc₂, pullback.condition]
      refine pt_inj e' (T := T) (by rw [Category.assoc, reassoc_of% hac, reassoc_of% hc₂,
        ← reassoc_of% pullback.condition]; rfl) rfl hq ?_
      let f : T ⟶ puncTarget π U qU := Over.homMk c (by
        simp only [T, Over.mk_hom]
        rw [reassoc_of% hc₂, ← reassoc_of% pullback.condition])
      have k := (pt_comp e' f a _).symm.trans ((congrArg (F.map f.op) hpt).trans
        (pt_comp eU f _ _))
      have k₂ := pt_puncMap π U e' eU T (𝟙 _) (Category.id_comp _)
      exact (k.trans ((pt_congr eU (by rw [Category.id_comp]; exact hc₁) _ _).trans k₂)).trans
        (pt_congr e' (Category.id_comp _) _ _)
    · rw [Category.id_comp, Category.assoc, hψ₂, hc₂]
  · -- `ψ ≫ puncComparison = 𝟙`
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hc₁]
      have hU : (ψ ≫ puncMap π U e' eU) ≫ qU = pullback.fst qU (π ∣_ U) ≫ qU := by
        rw [Category.assoc, puncMap_comp, pullback.condition, puncBase, ← Category.assoc, hψ₂]
      refine pt_inj eU (T := puncTarget π U qU) ?_ (pullback_fst_comp π U qU) hU ?_
      · rw [Category.assoc, reassoc_of% puncMap_comp, puncBase_ι]
        exact hψ
      · rw [← hpt]
        exact (pt_puncMap π U e' eU (puncTarget π U qU) ψ hψ).trans (pt_congr e' hψj _ _)
    · rw [Category.id_comp, Category.assoc, hc₂, hψ₂]

set_option backward.isDefEq.respectTransparency.types false in
/-- `puncMap` is affine when `π` is. -/
theorem isAffineHom_puncMap [IsAffineHom π] : IsAffineHom (puncMap π U e' eU) := by
  have := isIso_puncComparison π U e' eU
  have : IsAffineHom (π ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsAffineHom π› U
  have : IsAffineHom (pullback.fst qU (π ∣_ U)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback qU (π ∣_ U)).flip this
  have h : puncComparison π U e' eU ≫ pullback.fst qU (π ∣_ U) = puncMap π U e' eU :=
    pullback.lift_fst _ _ _
  rw [← h]
  infer_instance

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
