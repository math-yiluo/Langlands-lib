import Langlands.CommutativeAlgebra.DiagonalAutomorphismLocality
import Langlands.GroupScheme.Torus.DiagonalizablePower
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.HopfMorphismBaseChange

/-! # Locality of character automorphisms of diagonalizable group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Diagonalizable

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]

@[simp] theorem hopfSpecIso_hom_left :
    (hopfSpecIso R M).hom.hom.hom.left = 𝟙 (Spec (CommRingCat.of (AddMonoidAlgebra R M))) := by
  change Spec.map (𝟙 (CommRingCat.of (AddMonoidAlgebra R M))) = _
  simp only [Spec.map_id]

@[simp] theorem hopfSpecIso_inv_left :
    (hopfSpecIso R M).inv.hom.hom.left = 𝟙 (Spec (CommRingCat.of (AddMonoidAlgebra R M))) := by
  change Spec.map (𝟙 (CommRingCat.of (AddMonoidAlgebra R M))) = _
  simp only [Spec.map_id]

/-- Hopf coordinates of an actual isomorphism between diagonalizable groups. -/
def bialgEquivOfIso (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp) :
    AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M :=
  CommHopfAlgCat.ofIso
    (hopfSpec.fullyFaithful.preimageIso
      (hopfSpecIso R M ≪≫ e ≪≫ (hopfSpecIso R N).symm)).unop

theorem bialgEquivOfIso_hom_left
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp) :
    e.hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom (bialgEquivOfIso e).toAlgEquiv.toRingEquiv.toRingHom) := by
  have h := hopfSpec.fullyFaithful.map_preimage
    (hopfSpecIso R M ≪≫ e ≪≫ (hopfSpecIso R N).symm).hom
  have h' := congrArg (fun f => f.hom.hom.left) h
  change Spec.map (CommRingCat.ofHom
      (bialgEquivOfIso e).toAlgEquiv.toRingEquiv.toRingHom) =
    ((hopfSpecIso R M).hom.hom.hom.left ≫ e.hom.hom.hom.left) ≫
      (hopfSpecIso R N).inv.hom.hom.left at h'
  rw [hopfSpecIso_hom_left, hopfSpecIso_inv_left] at h'
  change Spec.map (CommRingCat.ofHom
      (bialgEquivOfIso e).toAlgEquiv.toRingEquiv.toRingHom) =
    ((𝟙 (groupScheme R M).X.left) ≫ e.hom.hom.hom.left) ≫
      𝟙 (groupScheme R N).X.left at h'
  simpa only [Category.id_comp, Category.comp_id] using h'.symm

open CommutativeAlgebra.DiagonalIsomorphismLocus

theorem scalarExtensionAlgHom_mapDomain
    (g : N →+ M) (C : Type u) [CommRing C] [Algebra R C] :
    scalarExtensionAlgHom (AddMonoidAlgebra.mapDomainAlgHom R R g) C =
      AddMonoidAlgebra.mapDomainAlgHom C C g := by
  apply AddMonoidAlgebra.algHom_ext
  · intro n
    simp
  · ext

/-- Equality in canonical scalar-extension coordinates detects equality of the
actual base-changed group morphisms. -/
theorem baseChange_hom_eq_restrictMap_of_scalarExtension_eq
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp)
    (C : Type u) [CommRing C] [Algebra R C] (g : N →+ M)
    (h : (scalarExtension (bialgEquivOfIso e).toBialgHom C).toAlgHom =
      AddMonoidAlgebra.mapDomainAlgHom C C g) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map e.hom =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
        (restrictMap R g) := by
  let f : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M :=
    (bialgEquivOfIso e).toAlgEquiv.toAlgHom
  let d : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M :=
    AddMonoidAlgebra.mapDomainAlgHom R R g
  have hcoord : scalarExtensionAlgHom f C = scalarExtensionAlgHom d C := by
    rw [scalarExtensionAlgHom_mapDomain]
    exact h
  have hmap : Algebra.TensorProduct.map (AlgHom.id C C) f =
      Algebra.TensorProduct.map (AlgHom.id C C) d := by
    apply Algebra.TensorProduct.ext'
    intro a b
    apply (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).injective
    have hh := DFunLike.congr_fun hcoord
      ((AddMonoidAlgebra.scalarTensorEquiv R C (M := N)) (a ⊗ₜ[R] b))
    simpa only [scalarExtensionAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply,
      HopfMorphismBaseChange.scalarExtension_eq] using hh
  have he : e.hom.hom.hom = (algSpec R).map (CommAlgCat.ofHom f).op :=
    Over.OverMorphism.ext (bialgEquivOfIso_hom_left e)
  have hd : (restrictMap R g).hom.hom = (algSpec R).map (CommAlgCat.ofHom d).op :=
    Over.OverMorphism.ext (restrictMap_left R g)
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
      e.hom.hom.hom).left =
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
      (restrictMap R g).hom.hom).left
  rw [he, hd]
  have hf := HopfMorphismBaseChange.tensorSpecIso_naturality (S := C) f
  have hd' := HopfMorphismBaseChange.tensorSpecIso_naturality (S := C) d
  rw [hmap] at hf
  exact hf.trans hd'.symm

/-- Every point of an affine base has a principal neighborhood where an actual
diagonalizable-group isomorphism is induced by one character equivalence. -/
theorem exists_away_eq_restrictMap [AddMonoid.FG N]
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp)
    (p : Ideal R) [p.IsPrime] :
    ∃ (g : N ≃+ M) (r : R), r ∉ p ∧
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r))))).map e.hom =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r))))).map
          (restrictMap R g.toAddMonoidHom) := by
  obtain ⟨g, r, hr, h⟩ :=
    CommutativeAlgebra.DiagonalAutomorphismLocality.exists_character_certificate_at_prime
      (bialgEquivOfIso e) p
  exact ⟨g, r, hr, baseChange_hom_eq_restrictMap_of_scalarExtension_eq e
    (Localization.Away r) g.toAddMonoidHom
      (h _ (IsLocalization.Away.algebraMap_isUnit r))⟩

/-- The character comparison commutes with restriction of characters. -/
theorem baseChangeIso_restrictMap {R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
    (g : N →+ M) :
    (GroupScheme.baseChange b).map (restrictMap R g) ≫ (baseChangeIso b N).hom =
      (baseChangeIso b M).hom ≫ restrictMap R' g := by
  apply hom_ext_points
  intro U x
  apply (characterPointsEquiv R' N U).injective
  apply MonoidHom.ext
  intro n
  change characterPointsEquiv R' N U
      ((x ≫ ((GroupScheme.baseChange b).map (restrictMap R g)).hom.hom) ≫
        (baseChangeIso b N).hom.hom.hom) (.ofAdd n.toAdd) =
    characterPointsEquiv R' N U
      ((x ≫ (baseChangeIso b M).hom.hom.hom) ≫ (restrictMap R' g).hom.hom)
        (.ofAdd n.toAdd)
  rw [characterPointsEquiv_baseChangeIso_hom]
  have hL : characterPointsEquiv R N ((Over.map b).obj U)
      (baseChangePointsEquiv b (groupScheme R M).toGrp U x ≫ (restrictMap R g).hom.hom)
      (.ofAdd n.toAdd) =
    characterPointsEquiv R M ((Over.map b).obj U)
      (baseChangePointsEquiv b (groupScheme R M).toGrp U x) (.ofAdd (g n.toAdd)) :=
    pointsEquiv_restrictMap R g _ n.toAdd
  have hR : characterPointsEquiv R' N U
      ((x ≫ (baseChangeIso b M).hom.hom.hom) ≫ (restrictMap R' g).hom.hom)
      (.ofAdd n.toAdd) =
    characterPointsEquiv R' M U (x ≫ (baseChangeIso b M).hom.hom.hom)
      (.ofAdd (g n.toAdd)) := pointsEquiv_restrictMap R' g _ n.toAdd
  change characterPointsEquiv R N ((Over.map b).obj U)
      (baseChangePointsEquiv b (groupScheme R N).toGrp U
        (x ≫ ((GroupScheme.baseChange b).map (restrictMap R g)).hom.hom))
        (.ofAdd n.toAdd) = _
  exact (congrArg (fun y => characterPointsEquiv R N ((Over.map b).obj U) y
      (.ofAdd n.toAdd)) (baseChangePointsEquiv_comp b (restrictMap R g) U x)).trans
    (hL.trans ((congrArg (fun χ => χ (.ofAdd (g n.toAdd)))
      (characterPointsEquiv_baseChangeIso_hom b M U x).symm).trans hR.symm))

/-- The affine locality statement in geometric neighborhood form. -/
theorem exists_open_neighborhood_eq_restrictMap [AddMonoid.FG N]
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp) (x : Spec R) :
    ∃ (C : CommRingCat.{u}) (a : Spec C ⟶ Spec R) (g : N ≃+ M),
      IsOpenImmersion a ∧ x ∈ Set.range a ∧
        (GroupScheme.baseChange a).map e.hom =
          (GroupScheme.baseChange a).map (restrictMap R g.toAddMonoidHom) := by
  obtain ⟨g, r, hr, h⟩ := exists_away_eq_restrictMap e x.asIdeal
  let a : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  refine ⟨CommRingCat.of (Localization.Away r), a, g, ?_, ?_, h⟩
  · exact IsOpenImmersion.of_isLocalization r
  · change PrimeSpectrum R at x
    change x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr

/-- Principal neighborhood and character equivalence data at a base point. -/
structure LocalCharacterModel
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp) (x : Spec R) where
  algebra : CommRingCat.{u}
  map : Spec algebra ⟶ Spec R
  character : N ≃+ M
  openImmersion : IsOpenImmersion map
  contains : x ∈ Set.range map
  equation :
        (GroupScheme.baseChange map).map e.hom =
          (GroupScheme.baseChange map).map (restrictMap R character.toAddMonoidHom)

/-- Choose the actual neighborhood and character data. -/
def localCharacterModel [AddMonoid.FG N]
    (e : (groupScheme R M).toGrp ≅ (groupScheme R N).toGrp) (x : Spec R) :
    LocalCharacterModel e x :=
  Classical.choice (by
    obtain ⟨C, a, g, ha, hx, he⟩ := exists_open_neighborhood_eq_restrictMap e x
    exact ⟨⟨C, a, g, ha, hx, he⟩⟩)

end Langlands.GroupScheme.Diagonalizable
