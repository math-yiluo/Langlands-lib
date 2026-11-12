import Langlands.GroupScheme.SmoothNormalizer.CutOut
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Closed normalizers of smooth connected subgroups over an affine base -/

universe u

open CategoryTheory TensorProduct AlgebraicGeometry Langlands.GroupScheme.Corepresented
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SmoothNormalizer

/-- Geometric connectedness of `Spec C → Spec R` gives connectedness of every field fibre
`Spec (K ⊗[R] C)`. -/
theorem connectedSpace_tensor_of_geometricallyConnected {R : CommRingCat.{u}} {C : Type u}
    [CommRing C] [Algebra R C]
    (h : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R C))))
    (K : Type u) [Field K] [Algebra R K] : ConnectedSpace (PrimeSpectrum (K ⊗[R] C)) := by
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)
  have := h.geometrically_connectedSpace (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    _ _ hpb.flip
  exact this

/-- **The affine case.** Over an affine base `Spec R`, the normalizer of a smooth closed subgroup
with geometrically connected fibres of a smooth affine group scheme is represented by a finitely
presented closed subgroup scheme. -/
theorem exists_normalizer_affine {R : CommRingCat.{u}} (G H : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hHs : Smooth H.X.hom) (hHc : GeometricallyConnected H.X.hom) :
    ∃ (N : GroupScheme (Spec R)) (j : N ⟶ G), IsClosedSubgroup j ∧
      LocallyOfFinitePresentation j.hom.hom.left ∧
        (SubgroupFunctor.range i).normalizer.IsRepresentedBy j := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  set j₀ := AffineCoordinates.coordinateHom i
  obtain ⟨I, hI⟩ := exists_ideal_range j₀
  have hcut := isCutOutBy_range hI
  -- `H` is isomorphic to the cut-out subgroup scheme `Spec (B ⧸ I)`.
  have hrange : SubgroupFunctor.range j₀ = SubgroupFunctor.range (cutHom hcut) := by
    rw [range_cutHom]
    refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
    exact mem_range_iff_mem_affineSubgroups hI x
  have hrep₁ : (SubgroupFunctor.range j₀).IsRepresentedBy j₀ :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrep₂ : (SubgroupFunctor.range j₀).IsRepresentedBy (cutHom hcut) :=
    ⟨inferInstance, hrange.symm⟩
  let eH : H ≅ cutGroupScheme hcut :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hrep₁ hrep₂
  have : IsIso eH.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eH.symm)).hom)
  have hX : (cutGroupScheme hcut).X.hom = eH.inv.hom.hom.left ≫ H.X.hom :=
    (Over.w eH.inv.hom.hom).symm
  have hsm : Algebra.Smooth R (AffineCoordinates.algebra G ⧸ I) := by
    rw [← smooth_groupScheme_iff (e := cutCorepresentableBy hcut)]
    change Smooth (cutGroupScheme hcut).X.hom
    rw [hX]
    infer_instance
  have hgc : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap R (AffineCoordinates.algebra G ⧸ I)))) := by
    change GeometricallyConnected (cutGroupScheme hcut).X.hom
    rw [hX]
    have hRI : MorphismProperty.RespectsIso (@GeometricallyConnected) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.precomp (P := @GeometricallyConnected) _ _ hHc
  have hconn := connectedSpace_tensor_of_geometricallyConnected hgc
  -- `I` is finitely generated.
  have hBs : Algebra.Smooth R (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  have hfgI : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective
      (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
    rwa [show RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I from Ideal.mk_ker] at h
  -- The normalizer is cut out by a finitely generated ideal.
  have hN := isCutOutBy_smoothNormalizerIdeal hcut hfgI hconn
  have hN' : IsCutOutBy (AffineCoordinates.corepresentation G)
      (affineSubgroups (SubgroupFunctor.range j₀).normalizer) (smoothNormalizerIdeal hcut) :=
    fun A g => by
      rw [affineSubgroups_normalizer hI A]
      exact hN A g
  have hNfg := smoothNormalizerIdeal_fg hcut hfgI hconn
  have hrepN : (SubgroupFunctor.range j₀).normalizer.IsRepresentedBy (cutHom hN') :=
    isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_of_isCutOutBy hN')
  have : IsClosedImmersion (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left :=
    IsClosedSubgroup.of_iso (AffineCoordinates.groupSchemeIso G)
  refine ⟨cutGroupScheme hN', cutHom hN' ≫ (AffineCoordinates.groupSchemeIso G).hom, ?_, ?_, ?_⟩
  · change IsClosedImmersion ((cutHom hN').hom.hom.left ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation ((cutHom hN').hom.hom.left ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left)
    have hcl : LocallyOfFinitePresentation (cutHom hN').hom.hom.left := by
      have h : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (smoothNormalizerIdeal hcut)))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
        refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
        rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
        exact hNfg
      rw [cutHom_left]
      exact h
    have : IsIso (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso
        ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))).hom)
    infer_instance
  · rw [SubgroupFunctor.normalizer_range_eq_comap_of_iso i (AffineCoordinates.groupSchemeIso G).symm]
    exact hrepN.comp_iso (AffineCoordinates.groupSchemeIso G)

end Langlands.GroupScheme.SmoothNormalizer
