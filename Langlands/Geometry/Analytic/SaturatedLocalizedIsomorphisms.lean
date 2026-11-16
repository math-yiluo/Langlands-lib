import Langlands.Geometry.Analytic.QuasiIsoTwoOutOfSix
import Langlands.Geometry.Analytic.SaturatedRightFractionComposition

/-! # Isomorphisms in the actual saturated localization -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- A fraction representing an identity has a full quasi-isomorphism numerator. -/
theorem isQuasiIso_of_localizedRightFraction_eq_id
    (φ : (quasiIsomorphisms (K := K)).RightFraction A A)
    (hφ : localizedRightFraction φ = 𝟙 _) : φ.f.IsQuasiIso := by
  have h0 : localizedRightFraction φ = localizedRightFraction
      (MorphismProperty.RightFraction.ofHom (quasiIsomorphisms (K := K)) (𝟙 A)) :=
    hφ.trans ((localizedRightFraction_ofHom (𝟙 A)).trans (localizationFunctor.map_id A)).symm
  obtain ⟨S, a, b, hden, hnum, hdenQ⟩ := (localizedRightFraction_eq_iff _ _).mp h0
  have ha := AffinoidAtlasPresentation.StrongHom.IsQuasiIso.of_saturatedComp_right
    (show φ.s.IsQuasiIso from φ.hs) S.hasAllLocalDomains φ.X'.hasAllLocalDomains hdenQ
  have he : a ≫ φ.f = a ≫ φ.s := hnum.trans hden.symm
  exact isQuasiIso_of_comp_left ha ((congrArg (fun m => m.IsQuasiIso) he).mpr hdenQ)

/-- The actual localization reflects isomorphisms into the full strong
quasi-isomorphism class. -/
theorem isQuasiIso_of_isIso_localizationFunctor_map (f : A ⟶ B)
    [IsIso (localizationFunctor.map f)] : f.IsQuasiIso := by
  let e := asIso (localizationFunctor.map f)
  obtain ⟨ψ, hψ⟩ := exists_localizedRightFraction e.inv
  let τ : (quasiIsomorphisms (K := K)).RightFraction B B :=
    ⟨ψ.s, ψ.hs, ψ.f ≫ f⟩
  have hτ : localizedRightFraction τ =
      localizedRightFraction ψ ≫ localizationFunctor.map f := by
    change (localizedQuasiIso ψ.s ψ.hs).inv ≫ localizationFunctor.map (ψ.f ≫ f) =
      ((localizedQuasiIso ψ.s ψ.hs).inv ≫ localizationFunctor.map ψ.f) ≫
        localizationFunctor.map f
    exact (congrArg (fun m => (localizedQuasiIso ψ.s ψ.hs).inv ≫ m)
      (localizationFunctor.map_comp ψ.f f)).trans (Category.assoc _ _ _).symm
  have hτid : localizedRightFraction τ = 𝟙 _ :=
    hτ.trans ((congrArg (fun m => m ≫ localizationFunctor.map f) hψ.symm).trans e.inv_hom_id)
  have hψf : (ψ.f ≫ f).IsQuasiIso := isQuasiIso_of_localizedRightFraction_eq_id τ hτid
  let ι := MorphismProperty.RightFraction.ofHom (quasiIsomorphisms (K := K)) f
  have hσid : localizedRightFraction (rightFractionComp ι ψ) = 𝟙 _ :=
    (localizedRightFraction_comp ι ψ).trans
      ((congrArg₂ (fun m n => m ≫ n) (localizedRightFraction_ofHom f) hψ.symm).trans
        e.hom_inv_id)
  have hσ := isQuasiIso_of_localizedRightFraction_eq_id (rightFractionComp ι ψ) hσid
  exact (isQuasiIso_twoOutOfSix (quasiIsoOreLift f ψ.s ψ.hs) ψ.f f hσ hψf).2.2

/-- Every localized isomorphism between presented objects has an actual
right fraction whose denominator and numerator are full quasi-isomorphisms. -/
def quasiIsoFractionOfIso
    (e : localizationFunctor.obj A ≅ localizationFunctor.obj B) :
    {φ : (quasiIsomorphisms (K := K)).RightFraction A B // φ.f.IsQuasiIso} := by
  let φ := rightFractionRepresentative e.hom
  have hmap : localizationFunctor.map φ.f = localizationFunctor.map φ.s ≫ e.hom :=
    (localizationFunctor_map_s_comp_localizedRightFraction φ).symm.trans
      (congrArg (fun m => localizationFunctor.map φ.s ≫ m)
        (localizedRightFraction_representative e.hom))
  haveI : IsIso (localizationFunctor.map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
  haveI : IsIso (localizationFunctor.map φ.f) :=
    hmap.symm ▸ (inferInstance : IsIso (localizationFunctor.map φ.s ≫ e.hom))
  exact ⟨φ, isQuasiIso_of_isIso_localizationFunctor_map φ.f⟩

@[simp]
theorem localizedRightFraction_quasiIsoFractionOfIso
    (e : localizationFunctor.obj A ≅ localizationFunctor.obj B) :
    localizedRightFraction (quasiIsoFractionOfIso e).val = e.hom :=
  localizedRightFraction_representative e.hom

end Langlands.Analytic.SaturatedAtlasPresentation
