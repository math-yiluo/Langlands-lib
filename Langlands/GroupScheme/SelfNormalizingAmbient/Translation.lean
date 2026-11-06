import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.SelfNormalizingAmbient.FibreDomain

/-! # Smooth closed subgroups of corepresented groups in algebra terms

See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Corepresented

/-- If `Spec S → Spec R` is smooth, then `S` is a smooth `R`-algebra. -/
theorem algebraSmooth_of_smooth_spec {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S)))) : Algebra.Smooth R S :=
  RingHom.smooth_algebraMap.1 (HasRingHomProperty.Spec_iff (P := @Smooth).1 h)

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- If the corepresented group scheme is smooth over `Spec R`, then its coordinate algebra is a
smooth `R`-algebra. -/
theorem smooth_of_smooth_groupScheme (h : Smooth (groupScheme F e).X.hom) :
    Algebra.Smooth R B :=
  algebraSmooth_of_smooth_spec h

/-- **A smooth closed subgroup with geometrically connected fibres** of a corepresented group
scheme is cut out on every test scheme by an ideal `I` of `B` such that `B ⧸ I` is a smooth
`R`-algebra whose fibres over all fields are domains. -/
theorem exists_ideal_range_smooth {K : GroupScheme (Spec R)} (j : K ⟶ groupScheme F e)
    [hj : IsClosedImmersion j.hom.hom.left] (hs : Smooth K.X.hom)
    (hc : GeometricallyConnected K.X.hom) :
    ∃ I : Ideal B, (∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
      y ∈ (SubgroupFunctor.range j).carrier U ↔
        ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0) ∧
      Algebra.Smooth R (B ⧸ I) ∧
      ∀ (k : Type u) [Field k] [Algebra R k], IsDomain (k ⊗[R] (B ⧸ I)) := by
  have hj' : IsClosedImmersion (j.hom.hom.left : K.X.left ⟶ Spec (CommRingCat.of B)) := hj
  obtain ⟨I, ε, hε⟩ : ∃ I : Ideal B, ∃ ε : K.X.left ≅ Spec (CommRingCat.of (B ⧸ I)),
      j.hom.hom.left = ε.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
    (IsClosedImmersion.Spec_iff (R := CommRingCat.of B) (f := j.hom.hom.left)).1 hj'
  have hw : K.X.hom = j.hom.hom.left ≫ (groupScheme F e).X.hom := (Over.w j.hom.hom).symm
  have h3 : ε.inv ≫ j.hom.hom.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
    (ε.inv ≫= hε).trans (Iso.inv_hom_id_assoc ε _)
  have h5 : Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Spec.map_comp]
    rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) = ε.inv ≫ K.X.hom :=
    (h5.trans (h3 =≫ _).symm).trans ((Category.assoc _ _ _).trans (congrArg (ε.inv ≫ ·) hw.symm))
  have hs' : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) := by
    rw [hq]
    have := hs
    infer_instance
  have hc' : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) := by
    rw [hq]
    have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.precomp @GeometricallyConnected.{u} ε.inv K.X.hom hc
  refine ⟨I, fun U y => ?_, algebraSmooth_of_smooth_spec hs', fun k _ _ =>
    SelfNormalizingAmbient.isDomain_tensor_of_smooth_geometricallyConnected hs' hc' k⟩
  simp only [homEquiv_symm_pointsEquiv_apply]
  have hfac := Langlands.AlgebraicGeometry.factorsThrough_affineQuotient_iff
    (A := CommRingCat.of B) I
    (y.left : U.left ⟶ Spec (CommRingCat.of B))
  rw [SubgroupFunctor.mem_range]
  refine Iff.trans ?_ (hfac.trans ⟨fun h b hb => h hb, fun h b hb => h b hb⟩)
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.left ≫ ε.hom, (Category.assoc _ _ _).trans (t.left ≫= hε.symm)⟩
  · rintro ⟨z, hz⟩
    have h4 : (z ≫ ε.inv) ≫ j.hom.hom.left = y.left :=
      (Category.assoc _ _ _).trans ((z ≫= h3).trans hz)
    refine ⟨Over.homMk (z ≫ ε.inv) ?_, ?_⟩
    · rw [hw, ← Category.assoc, h4]
      exact Over.w y
    · apply Over.OverMorphism.ext
      exact h4

end Langlands.GroupScheme.Corepresented
