import Langlands.AlgebraicGeometry.DvrStableNormalization.NormalLift

/-! # The normalization model of a scheme over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The relative normalization of `X` in its generic fibre, as a scheme over `Spec R`. -/
def source (X : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R)) :=
  Over.mk ((genericι X).fromNormalization ≫ X.hom)

/-- The normalization map, as a morphism over `Spec R`. -/
def map (X : Over (Spec (CommRingCat.of R))) : source X ⟶ X :=
  Over.homMk (genericι X).fromNormalization

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp]
lemma map_left (X : Over (Spec (CommRingCat.of R))) :
    (map X).left = (genericι X).fromNormalization := rfl

/-- Base change of the normalization map along the generic fibre inclusion is an isomorphism. -/
instance isIso_pullback_snd_fromNormalization (X : Over (Spec (CommRingCat.of R))) :
    IsIso (pullback.snd (genericι X).fromNormalization (genericι X)) := by
  set j := genericι X
  have h1 : IsIso (pullback.snd j j).fromNormalization := by
    have : IsIso ((pullback.snd j j).toNormalization ≫ (pullback.snd j j).fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsIso.of_isIso_comp_left (pullback.snd j j).toNormalization _
  have h2 : j.normalizationPullback j ≫ pullback.snd _ _ = (pullback.snd j j).fromNormalization :=
    Scheme.Hom.normalizationPullback_snd j j
  have h3 : pullback.snd j.fromNormalization j =
      inv (j.normalizationPullback j) ≫ (pullback.snd j j).fromNormalization := by
    rw [← h2, IsIso.inv_hom_id_assoc]
  rw [h3]; infer_instance

/-- The underlying morphism of the generic fibre of the normalization map is an isomorphism. -/
theorem isIso_genericMap_left (X : Over (Spec (CommRingCat.of R))) :
    IsIso ((Over.pullback (Spec.algebraMap R (FractionRing R))).map (map X)).left := by
  set j := genericι X
  let m : pullback (j.fromNormalization ≫ X.hom) (Spec.algebraMap R (FractionRing R)) ⟶
      pullback X.hom (Spec.algebraMap R (FractionRing R)) :=
    pullback.lift (pullback.fst _ _ ≫ j.fromNormalization) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  change IsIso m
  let e := pullbackRightPullbackFstIso X.hom (Spec.algebraMap R (FractionRing R))
    j.fromNormalization
  have key : e.hom ≫ m = pullback.snd j.fromNormalization j := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd]
  have hm : m = e.inv ≫ pullback.snd j.fromNormalization j := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [hm]; infer_instance

/-- The generic fibre of the normalization map is an isomorphism over the fraction field. -/
theorem genericIso (X : Over (Spec (CommRingCat.of R))) :
    IsIso ((Over.pullback (Spec.algebraMap R (FractionRing R))).map (map X)) :=
  (isIso_iff_of_reflects_iso _ (Over.forget _)).mp (isIso_genericMap_left X)

/-- Morphisms from the generic fibre of `T` into the source agree as soon as they agree after
composing with the normalization map. -/
theorem generic_eq_of_comp_eq (X T : Over (Spec (CommRingCat.of R)))
    (s₁ s₂ : T ⟶ source X) (hs : s₁.left ≫ (map X).left = s₂.left ≫ (map X).left) :
    genericι T ≫ s₁.left = genericι T ≫ s₂.left := by
  let m : pullback ((genericι X).fromNormalization ≫ X.hom) (Spec.algebraMap R (FractionRing R)) ⟶
      pullback X.hom (Spec.algebraMap R (FractionRing R)) :=
    pullback.lift (pullback.fst _ _ ≫ (genericι X).fromNormalization) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hm : IsIso m := isIso_genericMap_left X
  have hcond : ∀ s : T ⟶ source X,
      (genericι T ≫ s.left) ≫ ((genericι X).fromNormalization ≫ X.hom) =
        pullback.snd T.hom (Spec.algebraMap R (FractionRing R)) ≫
          Spec.algebraMap R (FractionRing R) := by
    intro s
    have hw : s.left ≫ ((genericι X).fromNormalization ≫ X.hom) = T.hom := Over.w s
    rw [Category.assoc, hw]
    exact pullback.condition
  let u (s : T ⟶ source X) : pullback T.hom (Spec.algebraMap R (FractionRing R)) ⟶
      pullback ((genericι X).fromNormalization ≫ X.hom) (Spec.algebraMap R (FractionRing R)) :=
    pullback.lift (genericι T ≫ s.left) (pullback.snd _ _) (hcond s)
  have hu1 : ∀ s, u s ≫ pullback.fst _ _ = genericι T ≫ s.left := fun s => pullback.lift_fst _ _ _
  have hu2 : ∀ s, u s ≫ pullback.snd _ _ = pullback.snd _ _ := fun s => pullback.lift_snd _ _ _
  have hm1 : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (genericι X).fromNormalization :=
    pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hu : u s₁ ≫ m = u s₂ ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hm1, reassoc_of% hu1, reassoc_of% hu1]
      exact congrArg (genericι T ≫ ·) hs
    · rw [Category.assoc, Category.assoc, hm2, hu2, hu2]
  have hu' : u s₁ = u s₂ := (cancel_mono m).mp hu
  rw [← hu1 s₁, ← hu1 s₂, hu']

/-- The lifting property of the normalization model for flat schemes with normal stalks. -/
theorem normal_lift (X T : Over (Spec (CommRingCat.of R))) [Flat T.hom]
    (hT : HasNormalStalks T.left) :
    Function.Bijective (fun f : T ⟶ source X => f ≫ map X) := by
  have hφ : IsIso (genericι T).fromNormalization := isIso_fromNormalization_of_normal T hT
  constructor
  · intro s₁ s₂ hs
    have hs' : s₁.left ≫ (map X).left = s₂.left ≫ (map X).left :=
      congrArg CommaMorphism.left hs
    have hgen := generic_eq_of_comp_eq X T s₁ s₂ hs'
    have hs'' : s₁.left ≫ (genericι X).fromNormalization =
        s₂.left ≫ (genericι X).fromNormalization := hs'
    have h₁ : 𝟙 T.left ≫ (s₁.left ≫ (genericι X).fromNormalization) =
        s₁.left ≫ (genericι X).fromNormalization := Category.id_comp _
    have h₂ : 𝟙 T.left ≫ (s₁.left ≫ (genericι X).fromNormalization) =
        s₂.left ≫ (genericι X).fromNormalization := by rw [Category.id_comp, hs'']
    let t₁ : T.left ⟶ pullback (s₁.left ≫ (genericι X).fromNormalization)
        (genericι X).fromNormalization := pullback.lift (𝟙 _) s₁.left h₁
    let t₂ : T.left ⟶ pullback (s₁.left ≫ (genericι X).fromNormalization)
        (genericι X).fromNormalization := pullback.lift (𝟙 _) s₂.left h₂
    have ht₁f : t₁ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
    have ht₂f : t₂ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
    have ht₁s : t₁ ≫ pullback.snd _ _ = s₁.left := pullback.lift_snd _ _ _
    have ht₂s : t₂ ≫ pullback.snd _ _ = s₂.left := pullback.lift_snd _ _ _
    have hext := Scheme.Hom.normalization.hom_ext (genericι T)
      ((genericι T).fromNormalization ≫ t₁) ((genericι T).fromNormalization ≫ t₂)
      (pullback.fst (s₁.left ≫ (genericι X).fromNormalization) (genericι X).fromNormalization)
      (by
        rw [Scheme.Hom.toNormalization_fromNormalization_assoc,
          Scheme.Hom.toNormalization_fromNormalization_assoc]
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, ht₁f, ht₂f]
        · rw [Category.assoc, Category.assoc, ht₁s, ht₂s]
          exact hgen)
      (by rw [Category.assoc, ht₁f, Category.comp_id])
      (by rw [Category.assoc, ht₂f, Category.comp_id])
    have ht : t₁ = t₂ := (cancel_epi (genericι T).fromNormalization).mp hext
    apply Over.OverMorphism.ext
    rw [← ht₁s, ← ht₂s, ht]
  · intro g
    have hgw : g.left ≫ X.hom = T.hom := Over.w g
    let ψ₀ : pullback T.hom (Spec.algebraMap R (FractionRing R)) ⟶
        pullback X.hom (Spec.algebraMap R (FractionRing R)) :=
      pullback.lift (genericι T ≫ g.left) (pullback.snd _ _)
        (by rw [Category.assoc, hgw]; exact pullback.condition)
    have hψ₀ : ψ₀ ≫ genericι X = genericι T ≫ g.left := pullback.lift_fst _ _ _
    let ψ : pullback T.hom (Spec.algebraMap R (FractionRing R)) ⟶ (genericι X).normalization :=
      ψ₀ ≫ (genericι X).toNormalization
    have hψ : genericι T ≫ g.left = ψ ≫ (genericι X).fromNormalization := by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ₀]
    let f₁ : pullback T.hom (Spec.algebraMap R (FractionRing R)) ⟶
        pullback g.left (genericι X).fromNormalization := pullback.lift (genericι T) ψ hψ
    have H : genericι T = f₁ ≫ pullback.fst g.left (genericι X).fromNormalization :=
      (pullback.lift_fst _ _ _).symm
    let d := (genericι T).normalizationDesc f₁ (pullback.fst g.left (genericι X).fromNormalization) H
    have hd : d ≫ pullback.fst g.left (genericι X).fromNormalization =
        (genericι T).fromNormalization :=
      Scheme.Hom.normalizationDesc_comp _ _ _ H
    let L : T.left ⟶ (genericι X).normalization :=
      inv (genericι T).fromNormalization ≫ d ≫ pullback.snd g.left (genericι X).fromNormalization
    have hL : L ≫ (genericι X).fromNormalization = g.left := by
      simp only [L, Category.assoc]
      rw [← pullback.condition, reassoc_of% hd, IsIso.inv_hom_id_assoc]
    have hLw : L ≫ (source X).hom = T.hom := by
      change L ≫ ((genericι X).fromNormalization ≫ X.hom) = T.hom
      rw [← Category.assoc, hL, hgw]
    refine ⟨Over.homMk L hLw, ?_⟩
    apply Over.OverMorphism.ext
    exact hL

end Langlands.AlgebraicGeometry.DvrStableNormalization
