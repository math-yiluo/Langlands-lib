import Langlands.AlgebraicGeometry.SchemeEtaleFlatLocalDescentProof
import Langlands.AlgebraicGeometry.SchemeEtaleLocus
import Langlands.AlgebraicGeometry.RelationSliceDifference
import Langlands.AlgebraicGeometry.RelationSliceEtalePropagationStatement

/-! # Propagation of etaleness on a relation slice -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry

namespace RelationSlice

open AlgebraicSpace.AtlasRelation

private lemma stalk_properties_of_etale_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) [Etale (W.ι ≫ f)]
    (x : X) (hx : x ∈ W) :
    (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified := by
  let z : W.toScheme := ⟨x, hx⟩
  have hf : ((W.ι ≫ f).stalkMap z).hom.Flat := Flat.stalkMap _ z
  have he : ((W.ι ≫ f).stalkMap z).hom.FormallyEtale :=
    (schemeEtaleLocus_eq_top (W.ι ≫ f)).ge (by trivial)
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hf he
  have hf' := (RingHom.Flat.respectsIso.cancel_right_isIso
    (f.stalkMap (W.ι z)) (W.ι.stalkMap z)).mp hf
  have he' := (formallyEtale_respectsIso.cancel_right_isIso
    (f.stalkMap (W.ι z)) (W.ι.stalkMap z)).mp he
  let := (f.stalkMap x).hom.toAlgebra
  have : Algebra.FormallyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := he'
  refine ⟨hf', ?_⟩
  change Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  infer_instance

/-- Etaleness at any section of the slice projection propagates to every
point over its etale locus. -/
lemma formallyEtale_stalkMap_of_section
    {U R V : Scheme.{u}} {t s : R ⟶ U} (hr : IsEquivRel t s)
    (g : V ⟶ U) [Flat s] [LocallyOfFinitePresentation (pullback.snd g t ≫ s)]
    (σ : V ⟶ pullback g t) (hσ : σ ≫ pullback.fst g t = 𝟙 V)
    (b : (pullback g t : Scheme.{u}))
    (hb : ((pullback.snd g t ≫ s).stalkMap (σ (pullback.fst g t b))).hom.FormallyEtale) :
    ((pullback.snd g t ≫ s).stalkMap b).hom.FormallyEtale := by
  let p := pullback.fst g t
  let h := pullback.snd g t ≫ s
  let D := pullback p p
  let q₁ : D ⟶ pullback g t := pullback.fst p p
  let q₂ : D ⟶ pullback g t := pullback.snd p p
  let d : D ⟶ R := difference hr g
  let k : pullback g t ⟶ D :=
    pullback.lift (p ≫ σ) (𝟙 _) (by simp [p, Category.assoc, hσ])
  have hk₁ : k ≫ q₁ = p ≫ σ := by simp [k, q₁]
  have hk₂ : k ≫ q₂ = 𝟙 _ := by simp [k, q₂]
  let W := schemeEtaleLocus h
  have hz : k b ∈ q₁ ⁻¹ᵁ W := by
    change q₁ (k b) ∈ W
    rw [← Scheme.Hom.comp_apply, hk₁, Scheme.Hom.comp_apply]
    exact hb
  have : Etale (W.ι ≫ h) := etale_schemeEtaleLocus h
  have H : IsPullback (q₁ ∣_ W) ((q₁ ⁻¹ᵁ W).ι ≫ d) (W.ι ≫ h) t :=
    (isPullback_morphismRestrict q₁ W).paste_vert (isPullback_difference_t hr g)
  have : Etale ((q₁ ⁻¹ᵁ W).ι ≫ d) :=
    MorphismProperty.of_isPullback H inferInstance
  obtain ⟨hflat, hur⟩ := stalk_properties_of_etale_open d (q₁ ⁻¹ᵁ W) (k b) hz
  have hdesc := schemeEtaleFlatLocalDescent _ _ _ _ h s q₂ d
    (isPullback_difference_s hr g) inferInstance inferInstance (k b) hflat hur
  have heq : q₂ (k b) = b := by
    rw [← Scheme.Hom.comp_apply, hk₂]
    rfl
  exact (congrArg (fun x => (h.stalkMap x).hom.FormallyEtale) heq).mp hdesc

/-- Shrinking the slicing scheme around an etale section point makes the
entire associated slice map etale. -/
lemma exists_open_etale_of_section
    {U R V : Scheme.{u}} {t s : R ⟶ U} (hr : IsEquivRel t s)
    (g : V ⟶ U) [Flat s] [LocallyOfFinitePresentation (pullback.snd g t ≫ s)]
    (σ : V ⟶ pullback g t) (hσ : σ ≫ pullback.fst g t = 𝟙 V)
    (v : V) (hv : ((pullback.snd g t ≫ s).stalkMap (σ v)).hom.FormallyEtale) :
    ∃ W : V.Opens, v ∈ W ∧ Etale (pullback.snd (W.ι ≫ g) t ≫ s) := by
  let h := pullback.snd g t ≫ s
  let W := σ ⁻¹ᵁ schemeEtaleLocus h
  refine ⟨W, hv, ?_⟩
  let a : pullback (W.ι ≫ g) t ⟶ pullback g t :=
    pullback.lift (pullback.fst _ _ ≫ W.ι) (pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
  have ha : a ≫ pullback.fst g t = pullback.fst (W.ι ≫ g) t ≫ W.ι := by
    simp [a]
  have Ha : IsPullback a (pullback.fst (W.ι ≫ g) t) (pullback.fst g t) W.ι := by
    apply IsPullback.of_right (h₁₂ := pullback.snd g t) (v₁₃ := t) ?_ ha
      (IsPullback.of_hasPullback g t).flip
    simpa only [a, pullback.lift_snd] using (IsPullback.of_hasPullback (W.ι ≫ g) t).flip
  have : IsOpenImmersion a := MorphismProperty.of_isPullback Ha.flip inferInstance
  have hah : a ≫ h = pullback.snd (W.ι ≫ g) t ≫ s := by
    simp only [h, a, pullback.lift_snd_assoc]
  rw [← hah]
  apply schemeEtaleLocus_eq_top_iff.mp
  rw [← top_le_iff]
  intro z _
  change ((a ≫ h).stalkMap z).hom.FormallyEtale
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  apply (formallyEtale_respectsIso.cancel_right_isIso _ (a.stalkMap z)).mpr
  apply formallyEtale_stalkMap_of_section hr g σ hσ (a z)
  have hp : pullback.fst g t (a z) = W.ι (pullback.fst (W.ι ≫ g) t z) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f z) ha
  change σ (pullback.fst g t (a z)) ∈ schemeEtaleLocus h
  rw [hp]
  exact (pullback.fst (W.ι ≫ g) t z).2

end RelationSlice

/-- The exact propagation and open shrinking proposition. -/
theorem relationSliceEtalePropagation : RelationSliceEtalePropagationStatement.{u} := by
  intro U R V t s hr g hs hh σ hσ v hv
  have := hs
  have := hh
  exact RelationSlice.exists_open_etale_of_section hr g σ hσ v hv

end Langlands.AlgebraicGeometry
