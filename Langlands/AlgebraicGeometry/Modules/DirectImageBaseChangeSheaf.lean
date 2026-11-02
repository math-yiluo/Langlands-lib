import Langlands.AlgebraicGeometry.Modules.OpenPushforwardSections
import Langlands.AlgebraicGeometry.Modules.AffineDirectImageBaseChange

/-! # Sheaf consequences of affine sections base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R T : CommRingCat.{u}} {X : Scheme.{u}}

/-- Relative sections over an affine presentation of an open are sections of the direct image
on that open, with their actual base-ring action. -/
def directImageRestrictionSectionsEquiv (φ : R ⟶ T) (f : X ⟶ Spec R)
    (V : (Spec R).Opens) (i : (V : Scheme) ⟶ Spec T) (hi : i ≫ Spec.map φ = V.ι)
    (M : X.Modules) :
    (ModuleCat.restrictScalars φ.hom).obj
      ((relativeGlobalSections ((f ∣_ V) ≫ i)).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M)) ≃ₗ[R]
      (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward f).obj M)).obj.obj (op V) := by
  let Q := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M
  have w : (f ∣_ V) ≫ V.ι = ((f ∣_ V) ≫ i) ≫ Spec.map φ := by
    rw [Category.assoc, hi]
  exact ((relativeGlobalSectionsBaseRingIso φ ((f ∣_ V) ≫ V.ι)
      ((f ∣_ V) ≫ i) w).app Q ≪≫
    ((relativeGlobalSectionsCompIso (f ∣_ V) V.ι).app Q).symm ≪≫
    (relativeGlobalSections V.ι).mapIso
      ((Scheme.Modules.pushforward (f ∣_ V)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M).symm) ≪≫
    (relativeGlobalSections V.ι).mapIso ((restrictPushforwardIso f V).app M)).toLinearEquiv ≪≫ₗ
      openPushforwardSectionsLinearEquiv ((Scheme.Modules.pushforward f).obj M) V

/-- The sections identification sends the ordinary base-change comparison to restriction. -/
lemma directImageRestrictionSectionsEquiv_sectionsBaseChangeMap
    (φ : R ⟶ T) (f : X ⟶ Spec R) (V : (Spec R).Opens)
    (i : (V : Scheme) ⟶ Spec T) (hi : i ≫ Spec.map φ = V.ι)
    (w : (f ⁻¹ᵁ V).ι ≫ f = ((f ∣_ V) ≫ i) ≫ Spec.map φ)
    (M : X.Modules) (x : (relativeGlobalSections f).obj M) :
    directImageRestrictionSectionsEquiv φ f V i hi M
      (sectionsBaseChangeMap φ f ((f ∣_ V) ≫ i) (f ⁻¹ᵁ V).ι w M x) =
        (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward f).obj M)).obj.map V.leTop.op x := by
  rw [sectionsBaseChangeMap_apply]
  change openPushforwardSectionsLinearEquiv ((Scheme.Modules.pushforward f).obj M) V
    (((restrictPushforwardIso f V).hom.app M).app (V.ι ⁻¹ᵁ ⊤)
      (((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).inv.app M).app
        ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ ⊤))
          (((Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι).unit.app M).app ⊤ x))) = _
  have hu := congrArg (fun k => k (show Γ(M, ⊤) from x))
    (pullback_unit_app_comp_restrictFunctorIsoPullback_inv (f ⁻¹ᵁ V).ι M ⊤)
  change (((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).inv.app M).app
    ((f ⁻¹ᵁ V).ι ⁻¹ᵁ ⊤))
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι).unit.app M).app ⊤ x) = _ at hu
  erw [hu]
  simp only [restrictPushforwardIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  change M.presheaf.map _
    (show Γ(M, f ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤))) from
      M.presheaf.map _
        (M.presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le ⊤)).op
          (show Γ(M, ⊤) from x))) =
    M.presheaf.map ((TopologicalSpace.Opens.map f.base).map V.leTop).op
      (show Γ(M, ⊤) from x)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- An invertible affine scalar comparison along an open immersion makes the actual
restriction map a module localization. -/
lemma isLocalizedModule_directImageRestriction [Algebra R T]
    (S : Submonoid R) [IsLocalization S T] (f : X ⟶ Spec R)
    (V : (Spec R).Opens) (i : (V : Scheme) ⟶ Spec T)
    (hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = V.ι)
    (w : (f ⁻¹ᵁ V).ι ≫ f = ((f ∣_ V) ≫ i) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (M : X.Modules)
    [IsIso (scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T))
      f ((f ∣_ V) ≫ i) (f ⁻¹ᵁ V).ι w M)] :
    IsLocalizedModule S
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward f).obj M)).obj.map V.leTop.op).hom := by
  let e := directImageRestrictionSectionsEquiv
    (CommRingCat.ofHom (algebraMap R T)) f V i hi M
  letI := isLocalizedModule_sectionsBaseChangeMap S f ((f ∣_ V) ≫ i)
    (f ⁻¹ᵁ V).ι w M
  have hl := IsLocalizedModule.of_linearEquiv S
    (sectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T))
      f ((f ∣_ V) ≫ i) (f ⁻¹ᵁ V).ι w M).hom e
  have hh : e.toLinearMap.comp
      (sectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T))
        f ((f ∣_ V) ≫ i) (f ⁻¹ᵁ V).ι w M).hom =
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward f).obj M)).obj.map V.leTop.op).hom := by
    ext x
    exact directImageRestrictionSectionsEquiv_sectionsBaseChangeMap
      (CommRingCat.ofHom (algebraMap R T)) f V i hi w M x
  rw [hh] at hl
  exact hl

/-- The principal-open affine base-change square commutes. -/
lemma principalOpenBaseChangeSquare (f : X ⟶ Spec R) (r : R) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ f =
      ((f ∣_ PrimeSpectrum.basicOpen r) ≫ (basicOpenIsoSpecAway r).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) := by
  rw [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  exact (isPullback_morphismRestrict f _).w.symm

/-- Principal-open scalar base change implies quasi-coherence of the actual direct image. -/
lemma isQuasicoherent_pushforward_of_isIso_principalOpenScalarSectionsBaseChangeMap
    (f : X ⟶ Spec R) (M : X.Modules)
    (h : ∀ r : R, IsIso (scalarSectionsBaseChangeMap
      (CommRingCat.ofHom (algebraMap R (Localization.Away r))) f
      ((f ∣_ PrimeSpectrum.basicOpen r) ≫ (basicOpenIsoSpecAway r).hom)
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι (principalOpenBaseChangeSquare f r) M)) :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).2
  apply (isIso_fromTildeΓ_iff_isLocalizing _).2
  intro r
  letI := h r
  exact isLocalizedModule_directImageRestriction (Submonoid.powers r) f
    (PrimeSpectrum.basicOpen r) (basicOpenIsoSpecAway r).hom
    (basicOpenIsoSpecAway_hom_SpecMap r) (principalOpenBaseChangeSquare f r) M

end Langlands.AlgebraicGeometry.Modules.DerivedSections
