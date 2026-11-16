import Langlands.Geometry.Analytic.SaturatedEtaleFractions
import Langlands.Geometry.Analytic.EtaleSite

/-! # Comparison with the existing localized étale predicate -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, v} K)

/-- At an original chart the reverse saturation comparison is the bounded
identity after identification of the chosen representative algebra. -/
theorem directFromSaturation_pullback_original_heq
    (i : A.atlas.Index)
    (h : A.directFromSaturation.baseMap ''
      Set.range (A.saturatedPresentation.atlas.chart (A.atlas.originalSaturatedIndex i)) ⊆
        Set.range (A.atlas.chart i)) :
    HEq (A.directFromSaturation.pullback (A.atlas.originalSaturatedIndex i) i h)
      (BoundedAlgHom.id K (A.atlas.algebra i)) := by
  have key : ∀ (U : LocalDomain A.atlas), U = A.atlas.originalLocalDomain i →
      ∀ p : U ⟶ A.atlas.originalLocalDomain i,
        HEq p.restriction (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    intro U hU p
    subst U
    exact heq_of_eq (congrArg LocalDomain.Inclusion.restriction
      (@Subsingleton.elim
        (LocalDomain.Inclusion (A.atlas.originalLocalDomain i) (A.atlas.originalLocalDomain i))
        inferInstance p (𝟙 (A.atlas.originalLocalDomain i))))
  exact key _ (A.atlas.saturatedRepresentative_original i) _

/-- At an original chart the forward saturation comparison is the bounded
identity after identification of the chosen target algebra. -/
theorem directToSaturation_pullback_original_heq
    (i : A.atlas.Index)
    (h : A.directToSaturation.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.saturatedPresentation.atlas.chart (A.atlas.originalSaturatedIndex i))) :
    HEq (A.directToSaturation.pullback i (A.atlas.originalSaturatedIndex i) h)
      (BoundedAlgHom.id K (A.atlas.algebra i)) := by
  have key : ∀ (U : LocalDomain A.atlas), U = A.atlas.originalLocalDomain i →
      ∀ p : A.atlas.originalLocalDomain i ⟶ U,
        HEq p.restriction (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    intro U hU p
    subst U
    exact heq_of_eq (congrArg LocalDomain.Inclusion.restriction
      (@Subsingleton.elim
        (LocalDomain.Inclusion (A.atlas.originalLocalDomain i) (A.atlas.originalLocalDomain i))
        inferInstance p (𝟙 (A.atlas.originalLocalDomain i))))
  exact key _ (A.atlas.saturatedRepresentative_original i) _

end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

variable {A B : SaturatedAtlasPresentation.{u, v, v} K}

/-- The actual saturation extension is the conjugate by the constructed
comparison isomorphisms, as equality of all bounded pullbacks. -/
theorem saturationExtension_eq_conjugate (f : A ⟶ B) :
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f =
      (A.saturationIso.hom ≫ f) ≫ B.saturationIso.inv := by
  let F := (A.saturationIso.hom ≫ f) ≫ B.saturationIso.inv
  symm
  apply f.saturationExtension_unique
    (f.hasCoherentPullbacks_of_saturated A.hasAllLocalDomains) F
  refine ⟨rfl, ?_⟩
  intro i j h
  let I := A.presentation.atlas.originalSaturatedIndex i
  let J := B.presentation.atlas.originalSaturatedIndex j
  have hAI : A.saturationIso.hom.baseMap ''
      Set.range (A.presentation.saturatedPresentation.atlas.chart I) ⊆
        Set.range (A.presentation.atlas.chart i) := by
    change id '' Set.range (A.presentation.atlas.saturatedChart I) ⊆
      Set.range (A.presentation.atlas.chart i)
    rw [Set.image_id, A.presentation.atlas.range_saturatedChart]
    exact Subset.rfl
  have hBJ : B.saturationIso.inv.baseMap '' Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (B.presentation.saturatedPresentation.atlas.chart J) := by
    change id '' Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (B.presentation.atlas.saturatedChart J)
    rw [Set.image_id, B.presentation.atlas.range_saturatedChart]
    exact Subset.rfl
  have hmid := A.saturationIso.hom.comp_admissible f I i j hAI h
  have hfinal := (A.saturationIso.hom ≫ f).comp_admissible B.saturationIso.inv I j J hmid hBJ
  change HEq (F.pullback I J hfinal) (f.pullback i j h)
  have hF : F.pullback I J hfinal =
      ((A.saturationIso.hom.pullback I i hAI).comp (f.pullback i j h)).comp
        (B.saturationIso.inv.pullback j J hBJ) := by
    exact (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
      (A.saturationIso.hom ≫ f) B.saturationIso.inv
      (SaturatedAtlasPresentation.ofSaturation A.presentation).hasAllLocalDomains
      B.hasAllLocalDomains I j J hmid hBJ hfinal).trans
        (congrArg (fun q => q.comp (B.saturationIso.inv.pullback j J hBJ))
          (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
            A.saturationIso.hom f
            (SaturatedAtlasPresentation.ofSaturation A.presentation).hasAllLocalDomains
            A.hasAllLocalDomains I i j hAI h hmid))
  have hleft := BoundedAlgHom.comp_heq
    (A.presentation.atlas.saturatedAtlas_original_algebra i) rfl rfl
    (A.presentation.directFromSaturation_pullback_original_heq i hAI)
    (heq_of_eq (rfl : f.pullback i j h = f.pullback i j h))
  have hboth := BoundedAlgHom.comp_heq
    (A.presentation.atlas.saturatedAtlas_original_algebra i) rfl
    (B.presentation.atlas.saturatedAtlas_original_algebra j) hleft
    (B.presentation.directToSaturation_pullback_original_heq j hBJ)
  exact (heq_of_eq hF).trans (hboth.trans (heq_of_eq (by
    rw [BoundedAlgHom.id_comp, BoundedAlgHom.comp_id])))

omit A B in
/-- The chosen actual saturation comparisons form a natural isomorphism
from canonical replacement to the original saturated category. -/
def saturationComparisonNatIso :
    (compatibleFunctor (K := K) ⋙ CompatibleAtlasPresentation.saturationFunctor) ≅
      𝟭 (SaturatedAtlasPresentation.{u, v, v} K) :=
  NatIso.ofComponents (fun A => A.saturationIso) (by
    intro A B f
    change ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f) ≫
      B.saturationIso.hom = A.saturationIso.hom ≫ f
    exact (congrArg (fun m => m ≫ B.saturationIso.hom)
      (saturationExtension_eq_conjugate f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => (A.saturationIso.hom ≫ f) ≫ m)
            B.saturationIso.inv_hom_id).trans (Category.comp_id _))))

/-- On a map between constructed saturations, the canonical strong property
agrees with the original all-pieces predicate. -/
theorem strongEtale_ofSaturation_iff
    {P Q : AffinoidAtlasPresentation.{u, v, v} K}
    (f : ofSaturation P ⟶ ofSaturation Q) :
    strongEtale f ↔ AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces
      (A := P) (B := Q) f := by
  unfold strongEtale
  rw [saturationExtension_eq_conjugate f]
  exact (AffinoidAtlasPresentation.StrongHom.isEtaleAllPieces_postcomp_quasiIso_iff
    (f := (ofSaturation P).saturationIso.hom ≫ f)
    (g := (ofSaturation Q).saturationIso.inv)
    Q.saturatedPresentation.isQuasiIso_directToSaturation).trans
      (AffinoidAtlasPresentation.StrongHom.isEtaleAllPieces_precomp_quasiIso_iff
        (f := (ofSaturation P).saturationIso.hom) (g := f)
        P.saturatedPresentation.isQuasiIso_directFromSaturation)

/-- Every canonically strong étale map gives an étale arrow for the existing
localized predicate. -/
theorem etale_map_of_strongEtale (f : A ⟶ B) (hf : strongEtale f) :
    etale (localizationFunctor.map f) := by
  have he : etale (localizationFunctor.map
      ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f)) :=
    etale_localizationFunctor_map _ hf
  have hconj := congrArg (fun m => etale (localizationFunctor.map m))
    (saturationExtension_eq_conjugate f)
  have h := hconj.mp he
  have hm : localizationFunctor.map ((A.saturationIso.hom ≫ f) ≫ B.saturationIso.inv) =
      (localizationFunctor.map A.saturationIso.hom ≫ localizationFunctor.map f) ≫
        localizationFunctor.map B.saturationIso.inv :=
    (localizationFunctor.map_comp (A.saturationIso.hom ≫ f) B.saturationIso.inv).trans
      (congrArg (fun m => m ≫ localizationFunctor.map B.saturationIso.inv)
        (localizationFunctor.map_comp A.saturationIso.hom f))
  have h' := (congrArg (fun m => etale m) hm).mp h
  exact ((etale (K := K)).cancel_left_of_respectsIso
    (localizationFunctor.map A.saturationIso.hom) (localizationFunctor.map f)).mp
      (((etale (K := K)).cancel_right_of_respectsIso _
        (localizationFunctor.map B.saturationIso.inv)).mp h')

/-- An étale numerator represents an étale arrow of the existing localization. -/
theorem etale_localizedRightFraction_of_strongEtale
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (hφ : strongEtale φ.f) : etale (localizedRightFraction φ) :=
  MorphismProperty.RespectsIso.precomp (etale (K := K))
    (localizedQuasiIso φ.s φ.hs).inv (localizationFunctor.map φ.f)
    (etale_map_of_strongEtale φ.f hφ)

/-- The intrinsic fraction property implies the existing site's étale property.
The reverse comparison is a separate obligation. -/
theorem localizedFractionEtale_le_etale :
    (localizedFractionEtale (K := K) :
      MorphismProperty (LocalizedCategory.{u, v, v} (K := K))) ≤ etale := by
  intro X Y f hf
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨φ, rfl, hφ⟩ := (localizedFractionEtale_iff f).mp hf
  exact etale_localizedRightFraction_of_strongEtale φ hφ

/-- The existing site's étale property is exactly the closure under arbitrary
arrow isomorphisms of the intrinsic fraction property. -/
theorem etale_eq_isoClosure_localizedFractionEtale :
    (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))) =
      (localizedFractionEtale (K := K)).isoClosure := by
  apply le_antisymm
  · intro X Y f hf
    obtain ⟨P, Q, g, hg, he⟩ := hf
    exact ⟨_, _, localizationFunctor.map g,
      (localizedFractionEtale_map_iff g).mpr ((strongEtale_ofSaturation_iff g).mpr hg), he⟩
  · exact (MorphismProperty.isoClosure_le_iff
      (localizedFractionEtale (K := K)) (etale (K := K))).mpr
        localizedFractionEtale_le_etale

end SaturatedAtlasPresentation
end Langlands.Analytic
