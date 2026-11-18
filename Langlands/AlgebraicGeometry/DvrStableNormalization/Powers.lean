import Langlands.AlgebraicGeometry.DvrStableNormalization.NormalStalks
import Langlands.AlgebraicGeometry.DvrStableNormalization.FlatSurjective
import Langlands.AlgebraicGeometry.DvrStableNormalizationStatement

/-! # Fibre powers of the normalization model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

section Paste

variable {C : Type*} [Category C] [HasPullbacks C]

/-- A pullback of `A ×_S B → A → S` along `y : T → S` is a pullback of `B → S` along
`A ×_S T → A → S`. -/
lemma isPullback_tensor {S A B T Z : C} (a : A ⟶ S) (b : B ⟶ S) (y : T ⟶ S)
    (fst : Z ⟶ pullback a b) (snd : Z ⟶ T) (h : IsPullback fst snd (pullback.fst a b ≫ a) y) :
    IsPullback (fst ≫ pullback.snd a b)
      (pullback.lift (fst ≫ pullback.fst a b) snd (by rw [Category.assoc]; exact h.w))
      b (pullback.fst a y ≫ a) := by
  have hq1 : pullback.lift (fst ≫ pullback.fst a b) snd (by rw [Category.assoc]; exact h.w) ≫
      pullback.fst a y = fst ≫ pullback.fst a b := pullback.lift_fst _ _ _
  have hq2 : pullback.lift (fst ≫ pullback.fst a b) snd (by rw [Category.assoc]; exact h.w) ≫
      pullback.snd a y = snd := pullback.lift_snd _ _ _
  have s : IsPullback (pullback.lift (fst ≫ pullback.fst a b) snd
      (by rw [Category.assoc]; exact h.w) ≫ pullback.snd a y) fst y (pullback.fst a b ≫ a) := by
    rw [hq2]; exact h.flip
  have L := IsPullback.of_right s hq1 (IsPullback.of_hasPullback a y).flip
  exact L.flip.paste_horiz (IsPullback.of_hasPullback a b).flip

end Paste

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The hypotheses of the normality criterion; they are stable under fibre products. -/
structure Good (P : Over (Spec (CommRingCat.of R))) : Prop where
  flat : Flat P.hom
  lft : LocallyOfFiniteType P.hom
  geomRed : GeometricallyReduced P.hom
  genSmooth : Smooth (pullback.snd P.hom (Spec.algebraMap R (FractionRing R)))

theorem Good.hasNormalStalks {P : Over (Spec (CommRingCat.of R))} (hP : Good P) :
    HasNormalStalks P.left := by
  have := hP.flat; have := hP.lft; have := hP.geomRed; have := hP.genSmooth
  exact hasNormalStalks_of_flat_of_geometricallyReduced P

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem Good.tensor {A B : Over (Spec (CommRingCat.of R))} (hA : Good A) (hB : Good B) :
    Good (A ⊗ B) := by
  have := hA.flat; have := hA.lft; have := hA.geomRed; have := hA.genSmooth
  have := hB.flat; have := hB.lft; have := hB.geomRed; have := hB.genSmooth
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · change LocallyOfFiniteType (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · change GeometricallyReduced (pullback.fst A.hom B.hom ≫ A.hom)
    constructor
    intro K _ y Z fst snd h
    have H := isPullback_tensor A.hom B.hom y fst snd h
    have : IsReduced (pullback A.hom y) :=
      GeometricallyReduced.geometrically_isReduced (f := A.hom) y (pullback.fst _ _)
        (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    have : IsReduced (pullback B.hom (pullback.fst A.hom y ≫ A.hom)) := inferInstance
    exact isReduced_of_isOpenImmersion H.isoPullback.hom
  · change Smooth (pullback.snd (pullback.fst A.hom B.hom ≫ A.hom)
      (Spec.algebraMap R (FractionRing R)))
    have H := isPullback_tensor A.hom B.hom (Spec.algebraMap R (FractionRing R))
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    set q := pullback.lift (pullback.fst (pullback.fst A.hom B.hom ≫ A.hom)
      (Spec.algebraMap R (FractionRing R)) ≫ pullback.fst A.hom B.hom)
      (pullback.snd (pullback.fst A.hom B.hom ≫ A.hom) (Spec.algebraMap R (FractionRing R)))
      (by rw [Category.assoc]; exact (IsPullback.of_hasPullback _ _).w) with hq
    have hq2 : q ≫ pullback.snd A.hom (Spec.algebraMap R (FractionRing R)) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    have hcomp : pullback.fst A.hom (Spec.algebraMap R (FractionRing R)) ≫ A.hom =
        pullback.snd A.hom (Spec.algebraMap R (FractionRing R)) ≫
          Spec.algebraMap R (FractionRing R) := pullback.condition
    rw [hcomp] at H
    let h₁₁ := pullback.lift (pullback.fst (pullback.fst A.hom B.hom ≫ A.hom)
      (Spec.algebraMap R (FractionRing R)) ≫ pullback.snd A.hom B.hom)
      (q ≫ pullback.snd A.hom (Spec.algebraMap R (FractionRing R)))
      (by simpa only [Category.assoc] using H.w)
    have h1 : h₁₁ ≫ pullback.fst B.hom (Spec.algebraMap R (FractionRing R)) =
        pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) (Spec.algebraMap R (FractionRing R)) ≫
          pullback.snd A.hom B.hom := pullback.lift_fst _ _ _
    have h2 : h₁₁ ≫ pullback.snd B.hom (Spec.algebraMap R (FractionRing R)) =
        q ≫ pullback.snd A.hom (Spec.algebraMap R (FractionRing R)) := pullback.lift_snd _ _ _
    have s' : IsPullback (h₁₁ ≫ pullback.fst B.hom (Spec.algebraMap R (FractionRing R))) q
        B.hom (pullback.snd A.hom (Spec.algebraMap R (FractionRing R)) ≫
          Spec.algebraMap R (FractionRing R)) := by
      rw [h1]; exact H
    have L := IsPullback.of_right s' h2
      (IsPullback.of_hasPullback B.hom (Spec.algebraMap R (FractionRing R)))
    have hqs : Smooth q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Smooth) L inferInstance
    rw [← hq2]
    infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem Good.positivePower {Y : Over (Spec (CommRingCat.of R))} (hY : Good Y) :
    ∀ n, Good (DvrStableNormalization.positivePower Y n)
  | 0 => hY
  | n + 1 => (Good.positivePower hY n).tensor hY

/-- The normalization model is good once its normalization map is finite and its fibres are
geometrically reduced. -/
theorem good_source (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom]
    [Smooth (pullback.snd X.hom (Spec.algebraMap R (FractionRing R)))]
    (hfin : IsFinite (map X).left) (hgr : GeometricallyReduced (source X).hom) :
    Good (source X) := by
  refine ⟨inferInstance, ?_, hgr, ?_⟩
  · change LocallyOfFiniteType ((genericι X).fromNormalization ≫ X.hom)
    have : IsFinite (genericι X).fromNormalization := hfin
    infer_instance
  · let m : pullback ((genericι X).fromNormalization ≫ X.hom)
        (Spec.algebraMap R (FractionRing R)) ⟶ pullback X.hom (Spec.algebraMap R (FractionRing R)) :=
      pullback.lift (pullback.fst _ _ ≫ (genericι X).fromNormalization) (pullback.snd _ _)
        (by rw [Category.assoc]; exact pullback.condition)
    have hm : IsIso m := isIso_genericMap_left X
    have hm2 : m ≫ pullback.snd X.hom (Spec.algebraMap R (FractionRing R)) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    change Smooth (pullback.snd ((genericι X).fromNormalization ≫ X.hom)
      (Spec.algebraMap R (FractionRing R)))
    rw [← hm2]
    infer_instance

end Langlands.AlgebraicGeometry.DvrStableNormalization
