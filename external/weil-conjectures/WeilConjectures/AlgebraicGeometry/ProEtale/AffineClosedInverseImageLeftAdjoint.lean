/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# An extra left adjoint for affine closed pro-etale inverse image

## References

* Stacks Project, Tag 09BL, clause (3), using Tag 09BK
* Stacks Project, Tag 09BL, clause (3), and Tag 09BK
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

-- Apply the existing small-site criterion after enlarging the Hom universes.
open CategoryTheory.Limits Opposite in
private theorem coveringCriterion
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (fStar : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
    (adj : R ⊣ fStar) [PreservesFiniteLimits R]
    (E : Set D)
    (hcover : ∀ V : D, ∃ S : Presieve V, Sieve.generate S ∈ K V ∧
      ∀ (W : D) (g : W ⟶ V), S g → W ∈ E)
    (hrep : ∀ V ∈ E, ∃ G : Sheaf J (Type (u + 1)),
      Nonempty (coyoneda.obj (op G) ≅
        R ⋙ (sheafSections K (Type (u + 1))).obj (op V))) :
    R.IsRightAdjoint := by
  let C' := ULiftHom.{u + 1} C
  let D' := ULiftHom.{u + 1} D
  let sC : C ≌ C' := ULiftHom.equiv
  let sD : D ≌ D' := ULiftHom.equiv
  let J' := sC.inverse.inducedTopology J
  let K' := sD.inverse.inducedTopology K
  have : sC.inverse.IsDenseSubsite J' J := by dsimp [J']; infer_instance
  have : sD.inverse.IsDenseSubsite K' K := by dsimp [K']; infer_instance
  let eC := sC.sheafCongr J J' (Type (u + 1))
  let eD := sD.sheafCongr K K' (Type (u + 1))
  let T := eC.inverse ⋙ R ⋙ eD.functor
  let Tstar := eD.inverse ⋙ fStar ⋙ eC.functor
  let adjT : T ⊣ Tstar :=
    (eC.symm.toAdjunction.comp adj).comp eD.toAdjunction
  have : PreservesFiniteLimits eC.inverse := inferInstance
  have : PreservesFiniteLimits eD.functor := inferInstance
  have : PreservesFiniteLimits (R ⋙ eD.functor) := comp_preservesFiniteLimits R eD.functor
  have : PreservesFiniteLimits T := comp_preservesFiniteLimits eC.inverse _
  have hJ : J'.toPrecoverage.toGrothendieck = J' := by
    refine le_antisymm J'.toGrothendieck_toPrecoverage_le ?_
    intro V S hS
    simpa using Precoverage.generate_mem_toGrothendieck
      ((J'.arrows_mem_toPrecoverage_iff S).mpr hS)
  have hK : K'.toPrecoverage.toGrothendieck = K' := by
    refine le_antisymm K'.toGrothendieck_toPrecoverage_le ?_
    intro V S hS
    simpa using Precoverage.generate_mem_toGrothendieck
      ((K'.arrows_mem_toPrecoverage_iff S).mpr hS)
  let E' : Set D' := {V | sD.inverse.obj V ∈ E}
  have hcover' : ∀ V : D', ∃ S : Presieve V, S ∈ K'.toPrecoverage V ∧
      ∀ (W : D') (g : W ⟶ V), S g → W ∈ E' := by
    intro V
    obtain ⟨S, hS, hE⟩ := hcover (sD.inverse.obj V)
    refine ⟨S.map sD.functor, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_toPrecoverage_iff,
        Sieve.generate_map_eq_functorPushforward]
      exact (CoverPreserving.of_isContinuous sD.functor K K').cover_preserve hS
    · intro W g hg
      rw [Presieve.map_iff] at hg
      obtain ⟨Y, hY, f, hf, -⟩ := hg
      subst W
      exact hE Y f hf
  have hrep' : ∀ V ∈ E', ∃ G : Sheaf J' (Type (u + 1)),
      Nonempty (coyoneda.obj (op G) ≅
        T ⋙ (sheafSections K' (Type (u + 1))).obj (op V)) := by
    intro V hV
    obtain ⟨G, ⟨e⟩⟩ := hrep (sD.inverse.obj V) hV
    refine ⟨eC.functor.obj G, ⟨?_⟩⟩
    exact (eC.toAdjunction.compCoyonedaIso.app (op G)) ≪≫
      Functor.isoWhiskerLeft eC.inverse e
  have : HasPullbacks C' := Adjunction.hasLimitsOfShape_of_equivalence sC.inverse
  have : HasPullbacks D' := Adjunction.hasLimitsOfShape_of_equivalence sD.inverse
  have criterion := exists_leftAdjoint_of_covering_corepresentable_evaluations.{u + 1, u + 1, 0}
    J'.toPrecoverage K'.toPrecoverage
  rw [hJ, hK] at criterion
  obtain ⟨L, ⟨hL⟩⟩ := criterion T Tstar adjT E' hcover' hrep'
  have : T.IsRightAdjoint := hL.isRightAdjoint
  have hR : (R ⋙ eD.functor).IsRightAdjoint :=
    (Functor.isRightAdjoint_comp_iff_right eC.inverse _).mp ‹T.IsRightAdjoint›
  exact (Functor.isRightAdjoint_comp_iff_left R eD.functor).mp hR
end CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Left exactness is proved on small models and transported by adjoint uniqueness.
open CategoryTheory.Limits Opposite in
private theorem inverseImage_finite {Z X : Scheme.{u}} (i : Z ⟶ X) :
    PreservesFiniteLimits (proEtaleSheafInverseImage i (Type (u + 1))) := by
  let sX : X.ProEt ≌ proEtaleSiteModel X := AsSmall.equiv
  let sZ : Z.ProEt ≌ proEtaleSiteModel Z := AsSmall.equiv
  have : sX.inverse.IsDenseSubsite (proEtaleModelTopology X) (ProEt.topology X) := by
    change sX.inverse.IsDenseSubsite (sX.inverse.inducedTopology (ProEt.topology X)) _
    infer_instance
  have : sZ.inverse.IsDenseSubsite (proEtaleModelTopology Z) (ProEt.topology Z) := by
    change sZ.inverse.IsDenseSubsite (sZ.inverse.inducedTopology (ProEt.topology Z)) _
    infer_instance
  let eX := sX.sheafCongr
    (ProEt.topology X) (proEtaleModelTopology X) (Type (u + 1))
  let eZ := sZ.sheafCongr
    (ProEt.topology Z) (proEtaleModelTopology Z) (Type (u + 1))
  let B := (proEtaleModelBaseChange i).sheafPullback (Type (u + 1))
    (proEtaleModelTopology X) (proEtaleModelTopology Z)
  have : HasFiniteLimits (proEtaleSiteModel X) := inferInstance
  have : PreservesFiniteLimits (proEtaleModelBaseChange i) := by
    exact comp_preservesFiniteLimits sX.inverse
      (proEtaleBaseChange i ⋙ sZ.functor)
  have : RepresentablyFlat (proEtaleModelBaseChange i) :=
    flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits ((proEtaleModelBaseChange i).op.lan :
      ((proEtaleSiteModel X)ᵒᵖ ⥤ Type (u + 1)) ⥤
      (proEtaleSiteModel Z)ᵒᵖ ⥤ Type (u + 1)) := by
    apply lan_preservesFiniteLimits_of_flat
  have : PreservesFiniteLimits B :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits
      (proEtaleModelBaseChange i) (Type (u + 1))
        (proEtaleModelTopology X) (proEtaleModelTopology Z)
  let adj := (eX.toAdjunction.comp
    ((proEtaleModelBaseChange i).sheafAdjunctionContinuous (Type (u + 1))
      (proEtaleModelTopology X) (proEtaleModelTopology Z))).comp eZ.symm.toAdjunction
  let t : eZ.functor ⋙
      (proEtaleModelBaseChange i).sheafPushforwardContinuous (Type (u + 1))
        (proEtaleModelTopology X) (proEtaleModelTopology Z) ⋙ eX.inverse ≅
      proEtaleSheafDirectImage i (Type (u + 1)) :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro F G f
      rfl)
  let h := (proEtaleSheafAdjunction i (Type (u + 1))).leftAdjointUniq
    (adj.ofNatIsoRight t)
  exact preservesFiniteLimits_of_natIso h.symm
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.AffineProEt

open CategoryTheory.Limits Opposite in
private noncomputable def evaluationCorepresentable (S : Scheme.{u}) (U : S.ProEt) :
    coyoneda.obj (op ((presheafToSheaf (ProEt.topology S) (Type (u + 1))).obj
      (uliftYoneda.{u + 1}.obj U))) ≅
        (sheafSections (ProEt.topology S) (Type (u + 1))).obj (op U) :=
  NatIso.ofComponents
    (fun F ↦ Equiv.toIso
      (((sheafificationAdjunction (ProEt.topology S) (Type (u + 1))).homEquiv _ F).trans
        uliftYonedaEquiv))
    (by
      intro F G f
      ext a
      change uliftYonedaEquiv
          ((sheafificationAdjunction (ProEt.topology S) (Type (u + 1))).homEquiv _ G
            (a ≫ f)) = _
      rw [Adjunction.homEquiv_naturality_right, uliftYonedaEquiv_comp]
      rfl)

open CategoryTheory.Limits Opposite in
private theorem quotient_corepresentable (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1)))
      (f : P ⟶ Q), Epi f → Function.Surjective (f.hom.app (op V))) :
    ∃ G : Sheaf (ProEt.topology (Spec (.of A))) (Type (u + 1)),
      Nonempty (coyoneda.obj (op G) ≅
        (proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
            (Type (u + 1)) ⋙
          (toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous (Type (u + 1))
            (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I))))) ⋙
        (sheafSections (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))).obj (op V)) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let v := closedSiteLift A I ⋙ toProEt X
  let P := sheafToPresheaf (ProEt.topology X) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ (Type (u + 1))).obj v.op
  let E := (sheafSections (topology Z) (Type (u + 1))).obj (op V)
  let η : (sheafSections (ProEt.topology X) (Type (u + 1))).obj (op (v.obj V)) ⟶
      (P ⋙ presheafToSheaf (topology Z) (Type (u + 1))) ⋙ E :=
    { app := fun F ↦ (toSheafify (topology Z) (P.obj F)).app (op V)
      naturality := by
        intro F G f
        exact congr_app (toSheafify_naturality (topology Z) (P.map f)) (op V) }
  have hη (F : Sheaf (ProEt.topology X) (Type (u + 1))) : IsIso (η.app F) := by
    rw [isIso_iff_bijective]
    exact (affine_closed_inverseImage_evaluation A I).2 F V hV
  have : IsIso η := NatIso.isIso_of_isIso_app η
  obtain ⟨e⟩ := (affine_closed_inverseImage_evaluation A I).1
  refine ⟨_, ⟨evaluationCorepresentable X (v.obj V) ≪≫ asIso η ≪≫
    (Functor.isoWhiskerRight e E).symm⟩⟩
end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits Opposite in
private noncomputable def inverseImageComp {T Z X : Scheme.{u}} (f : T ⟶ Z) (g : Z ⟶ X) :
    proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        proEtaleSheafInverseImage f (Type (u + 1)) :=
  (proEtaleSheafAdjunction (f ≫ g) (Type (u + 1))).leftAdjointUniq
    (((proEtaleSheafAdjunction g (Type (u + 1))).comp
      (proEtaleSheafAdjunction f (Type (u + 1)))).ofNatIsoRight
        (ProEtale.lowerStarComp (Type (u + 1)) f g))

open CategoryTheory.Limits Opposite in
private theorem inverseImageIso_isEquivalence {Z X : Scheme.{u}} (e : Z ≅ X) :
    (proEtaleSheafInverseImage e.hom (Type (u + 1))).IsEquivalence := by
  let h := (proEtaleSheafAdjunction e.hom (Type (u + 1))).leftAdjointUniq
    (ProEtale.lowerStarEquivalence (Type (u + 1)) e).symm.toAdjunction
  exact Functor.isEquivalence_of_iso h.symm

open CategoryTheory.Limits Opposite in
private theorem reduce_to_quotient
    (H : ∀ (A : Type u) [CommRing A] (I : Ideal A),
      (proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Type (u + 1))).IsRightAdjoint)
    {Z X : Scheme.{u}} [IsAffine Z] [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    (proEtaleSheafInverseImage i (Type (u + 1))).IsRightAdjoint := by
  obtain ⟨I, e, hi⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion (i ≫ X.isoSpec.hom))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hq : (proEtaleSheafInverseImage q (Type (u + 1))).IsRightAdjoint := H _ I
  have he := inverseImageIso_isEquivalence e
  have hx : (proEtaleSheafInverseImage X.isoSpec.inv (Type (u + 1))).IsEquivalence :=
    inverseImageIso_isEquivalence X.isoSpec.symm
  have hi' : i = (e.hom ≫ q) ≫ X.isoSpec.inv := by
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi']
  have hinner : (proEtaleSheafInverseImage (e.hom ≫ q) (Type (u + 1))).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (inverseImageComp _ _).symm
  have : (proEtaleSheafInverseImage X.isoSpec.inv (Type (u + 1))).IsRightAdjoint :=
    inferInstance
  have : (proEtaleSheafInverseImage X.isoSpec.inv (Type (u + 1)) ⋙
      proEtaleSheafInverseImage (e.hom ≫ q) (Type (u + 1))).IsRightAdjoint :=
    inferInstance
  exact Functor.isRightAdjoint_of_iso (inverseImageComp (e.hom ≫ q) X.isoSpec.inv).symm

open CategoryTheory.Limits Opposite in
private theorem quotientInverseImage_isRightAdjoint
    (A : Type u) [CommRing A] (I : Ideal A) :
    (proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Type (u + 1))).IsRightAdjoint := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let res := (AffineProEt.toProEt Z).sheafPushforwardContinuous (Type (u + 1))
    (AffineProEt.topology Z) (ProEt.topology Z)
  let e := res.asEquivalence
  let R := proEtaleSheafInverseImage q (Type (u + 1)) ⋙ res
  let star := e.inverse ⋙ proEtaleSheafDirectImage q (Type (u + 1))
  have adjR : R ⊣ star := (proEtaleSheafAdjunction q (Type (u + 1))).comp e.toAdjunction
  have : PreservesFiniteLimits (proEtaleSheafInverseImage q (Type (u + 1))) :=
    inverseImage_finite q
  have : PreservesFiniteLimits R := comp_preservesFiniteLimits _ _
  let E : Set Z.AffineProEt := {V | ∀ (P Q :
    Sheaf (AffineProEt.topology Z) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V))}
  have hcover : ∀ V : Z.AffineProEt, ∃ S : Presieve V,
      Sieve.generate S ∈ AffineProEt.topology Z V ∧
      ∀ (W : Z.AffineProEt) (g : W ⟶ V), S g → W ∈ E := by
    intro V
    obtain ⟨ι, W, f, hcov, hW⟩ := AffineProEt.exists_weaklyContractible_cover Z V
    refine ⟨Presieve.ofArrows W f, ?_, ?_⟩
    · apply (AffineProEt.toProEt Z).mem_restrictedTopology_of_functorPushforward_mem
      rw [← Sieve.generate_map_eq_functorPushforward]
      apply Precoverage.generate_mem_toGrothendieck
      simpa only [AffineProEt.precoverage, ProEt.precoverage,
        Precoverage.mem_comap_iff, Presieve.map_comp, Functor.comp_obj] using hcov
    · intro W' g hg
      cases hg with
      | mk j => exact hW j
  have hrep : ∀ V ∈ E, ∃ G : Sheaf (ProEt.topology X) (Type (u + 1)),
      Nonempty (coyoneda.obj (op G) ≅
        R ⋙ (sheafSections (AffineProEt.topology Z) (Type (u + 1))).obj (op V)) := by
    intro V hV
    exact AffineProEt.quotient_corepresentable A I V hV
  have hR : R.IsRightAdjoint := CategoryTheory.coveringCriterion
    (ProEt.topology X) (AffineProEt.topology Z) R star adjR E hcover hrep
  exact (Functor.isRightAdjoint_comp_iff_left
    (proEtaleSheafInverseImage q (Type (u + 1))) res).mp hR

/-- The ordinary inverse image on set-valued small pro-etale sheaves for a closed
immersion of affine schemes has a left adjoint. The adjunction provides the bijections
`Hom(L G, F) ≃ Hom(G, i⁻¹ F)`, natural in both `G` and `F`.
-/
theorem exists_affineClosedInverseImageLeftAdjoint {Z X : Scheme.{u}}
    [IsAffine Z] [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ L : Sheaf (ProEt.topology Z) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology X) (Type (u + 1)),
      Nonempty (L ⊣ proEtaleSheafInverseImage i (Type (u + 1))) := by
  have : (proEtaleSheafInverseImage i (Type (u + 1))).IsRightAdjoint :=
    reduce_to_quotient quotientInverseImage_isRightAdjoint i
  exact Functor.IsRightAdjoint.exists_leftAdjoint

end AlgebraicGeometry.Scheme
