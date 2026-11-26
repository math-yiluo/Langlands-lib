import Langlands.GroupScheme.Dilatation.ResidueGeometry
import Langlands.GroupScheme.Dilatation.StructureReduction

/-! # Structural properties of group scheme dilatations over a DVR -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open Dilatation
open Langlands.AlgebraicGeometry (affineQuotientPullbackIso affineQuotientPullbackIso_hom_fst)
open Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus (coordinateIso)

universe u

section SpecReduction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (A : Type u) [CommRing A] [Algebra R A]

private abbrev quotientMax := (IsLocalRing.maximalIdeal R).map (algebraMap R A)

private instance quotientMaxAlgebra :
    Algebra (IsLocalRing.ResidueField R) (A ⧸ quotientMax (R := R) A) :=
  @RingHom.toAlgebra (IsLocalRing.ResidueField R) (A ⧸ quotientMax (R := R) A) _ _
    (Ideal.quotientMap (quotientMax (R := R) A) (algebraMap R A) Ideal.le_comap_map)

private theorem quotientMax_eq {r : R} (hr : Irreducible r) :
    quotientMax (R := R) A = Ideal.span {algebraMap R A r} := by
  rw [quotientMax, hr.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

private def specialSpecIso :
    Spec (CommRingCat.of (A ⧸ quotientMax (R := R) A)) ≅
      pullback (Spec.algebraMap R A) (residueBaseMap R) :=
  affineQuotientPullbackIso (algebraMap R A) (IsLocalRing.maximalIdeal R) ≪≫
    pullbackSymmetry (residueBaseMap R) (Spec.algebraMap R A)

private theorem specialSpecIso_hom_snd :
    (specialSpecIso (R := R) A).hom ≫ pullback.snd (Spec.algebraMap R A) (residueBaseMap R) =
      Spec.algebraMap (IsLocalRing.ResidueField R) (A ⧸ quotientMax (R := R) A) := by
  rw [specialSpecIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact affineQuotientPullbackIso_hom_fst (algebraMap R A) (IsLocalRing.maximalIdeal R)

private theorem specialSpec_hom_overBase :
    Spec.algebraMap (IsLocalRing.ResidueField R) (A ⧸ quotientMax (R := R) A) ≫
        residueBaseMap R = Spec.algebraMap R (A ⧸ quotientMax (R := R) A) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R)
    (A ⧸ quotientMax (R := R) A))) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) = _
  rw [← Spec.map_comp]
  rfl

private def principalSpecialSpecIso {r : R} (hr : Irreducible r) :
    Spec (CommRingCat.of (A ⧸ Ideal.span {algebraMap R A r})) ≅
      pullback (Spec.algebraMap R A) (residueBaseMap R) :=
  Scheme.Spec.mapIso (Ideal.quotEquivOfEq (quotientMax_eq A hr)).toCommRingCatIso.op ≪≫
    specialSpecIso (R := R) A

private theorem principalSpecialSpecIso_hom_overBase {r : R} (hr : Irreducible r) :
    (principalSpecialSpecIso A hr).hom ≫ pullback.snd (Spec.algebraMap R A) (residueBaseMap R) ≫
        residueBaseMap R = Spec.algebraMap R (A ⧸ Ideal.span {algebraMap R A r}) := by
  rw [principalSpecialSpecIso, Iso.trans_hom, Category.assoc, ← Category.assoc
    (specialSpecIso (R := R) A).hom, specialSpecIso_hom_snd, specialSpec_hom_overBase]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Ideal.quotEquivOfEq_mk (quotientMax_eq A hr) (algebraMap R A x)

private theorem regular_principal_special {r : R} (hr : Irreducible r)
    (h : Smooth (Spec.algebraMap R A)) :
    IsRegularRing (A ⧸ Ideal.span {algebraMap R A r}) := by
  let : Smooth (Spec.algebraMap R A) := h
  have hs : Smooth (Spec.algebraMap (IsLocalRing.ResidueField R) (A ⧸ quotientMax (R := R) A)) := by
    rw [← specialSpecIso_hom_snd]
    infer_instance
  let : IsRegularRing (A ⧸ quotientMax (R := R) A) := isRegularRing_of_smoothSpec hs
  exact IsRegularRing.of_ringEquiv (Ideal.quotEquivOfEq (quotientMax_eq A hr))

end SpecReduction

section Centre

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Over (Spec (CommRingCat.of R))} [IsAffine X.left]
  {Y : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  (j : Y ⟶ (Over.pullback (residueBaseMap R)).obj X) [IsClosedImmersion j.left]

private instance : IsClosedImmersion (residueBaseMap R) :=
  inferInstanceAs (IsClosedImmersion (quotientBase (IsLocalRing.maximalIdeal R)))

private abbrev centreOverBase := (Over.map (residueBaseMap R)).obj Y

private def centreSpecOverIso :
    algebraSpec (R := R) (affineAlgebra X ⧸ centreIdeal j) ≅ centreOverBase (Y := Y) := by
  let h := IsClosedImmersion.isAffine_surjective_of_isAffine (centreInclusion j).left
  let : IsAffine (centreOverBase (Y := Y)).left := h.1
  exact (algSpec (CommRingCat.of R)).mapIso (CommAlgCat.isoMk
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := affineAlgebraMap (centreInclusion j)) h.2).symm).op ≪≫
    (coordinateIso (CommRingCat.of R) (centreOverBase (Y := Y))).symm

private theorem centreSpecOverIso_hom_overBase :
    ((centreSpecOverIso j).hom.left ≫ Y.hom) ≫ residueBaseMap R =
      Spec.algebraMap R (affineAlgebra X ⧸ centreIdeal j) := by
  rw [Category.assoc]
  exact (centreSpecOverIso j).hom.w

private theorem centre_contains_uniformizer {r : R} (hr : Irreducible r) :
    algebraMap R (affineAlgebra X) r ∈ centreIdeal j := by
  let Q := affineAlgebra X ⧸ centreIdeal j
  let f := (centreSpecOverIso j).hom.left ≫ Y.hom
  have hf : Spec.map (Spec.preimage f) = f := Spec.map_preimage f
  have h := centreSpecOverIso_hom_overBase j
  change f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) =
    Spec.map (CommRingCat.ofHom (algebraMap R Q)) at h
  rw [← hf, ← Spec.map_comp] at h
  have he := Spec.map_injective h
  have hπ : IsLocalRing.residue R r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hr.maximalIdeal_eq.symm ▸ Ideal.subset_span (Set.mem_singleton r))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change algebraMap R Q r = 0
  have hh := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of Q => k.hom r) he
  change (Spec.preimage f).hom (IsLocalRing.residue R r) = algebraMap R Q r at hh
  rw [← hh, hπ, map_zero]

private theorem regular_centre (hY : Smooth Y.hom) : IsRegularRing (affineAlgebra X ⧸ centreIdeal j) := by
  let Q := affineAlgebra X ⧸ centreIdeal j
  let f := (centreSpecOverIso j).hom.left ≫ Y.hom
  let : Algebra (IsLocalRing.ResidueField R) Q :=
    @RingHom.toAlgebra (IsLocalRing.ResidueField R) Q _ _ (Spec.preimage f).hom
  let : IsIso (centreSpecOverIso j).hom.left := (Over.forget _).map_isIso (centreSpecOverIso j).hom
  let : Smooth f := MorphismProperty.RespectsIso.precomp @Smooth _ _ hY
  have h : Spec.algebraMap (IsLocalRing.ResidueField R) Q = f := Spec.map_preimage _
  exact isRegularRing_of_smoothSpec (h.symm ▸ ‹Smooth f›)

end Centre

/-- Smoothness and geometric connectedness for the dilatation along a smooth
centre in the special fibre of a smooth affine DVR group model. -/
theorem smoothDilatation : SmoothDilatationStatement.{u} := by
  intro R K _ _ _ _ _ _ G M r hr Y j hj hM hY
  let X := M.group.X
  let b := residueBaseMap R
  let j₀ : Y.X ⟶ (Over.pullback b).obj X := j.hom.hom
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let A := affineAlgebra X
  let I := centreIdeal j₀
  let B := (blowupAlgebra r I : Type u)
  let C := blowupResidue r I
  let Q := A ⧸ I
  let D := M.dilatation hr j
  let : IsClosedImmersion j₀.left := hj
  let : Module.Flat R A := (affineAlgebra_flat_iff X).mpr inferInstance
  let : Algebra.FiniteType R A := (affineAlgebra_finiteType_iff X).mpr inferInstance
  let : IsIso (coordinateIso (CommRingCat.of R) X).inv.left :=
    (Over.forget _).map_isIso (coordinateIso _ X).inv
  have hA : Smooth (Spec.algebraMap R A) := by
    have he : (coordinateIso (CommRingCat.of R) X).inv.left ≫ X.hom = Spec.algebraMap R A :=
      (coordinateIso _ X).inv.w
    rw [← he]
    exact MorphismProperty.RespectsIso.precomp @Smooth _ _ hM
  let : IsRegularRing (A ⧸ Ideal.span {algebraMap R A r}) := regular_principal_special A hr hA
  let : IsRegularRing Q := regular_centre j₀ hY
  have hI : algebraMap R A r ∈ I := centre_contains_uniformizer j₀ hr
  let eD : Spec (CommRingCat.of C) ≅ D.specialFibre.X.left := principalSpecialSpecIso B hr
  let eY : Spec (CommRingCat.of Q) ≅ Y.X.left :=
    (Over.forget _).mapIso (centreSpecOverIso j₀)
  let f₀ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of Q) := Spec.algebraMap Q C
  have hR : f₀ ≫ Spec.algebraMap R Q = Spec.algebraMap R C := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  let : Mono b := by
    change Mono (quotientBase (IsLocalRing.maximalIdeal R))
    infer_instance
  have hw : f₀ ≫ eY.hom ≫ Y.X.hom = eD.hom ≫ D.specialFibre.X.hom := by
    apply (cancel_mono b).mp
    have hy : (eY.hom ≫ Y.X.hom) ≫ b = Spec.algebraMap R Q := centreSpecOverIso_hom_overBase j₀
    have hd : eD.hom ≫ D.specialFibre.X.hom ≫ b = Spec.algebraMap R C :=
      principalSpecialSpecIso_hom_overBase B hr
    calc
      _ = f₀ ≫ ((eY.hom ≫ Y.X.hom) ≫ b) := Category.assoc _ _ _
      _ = Spec.algebraMap R C := (congrArg (f₀ ≫ ·) hy).trans hR
      _ = _ := hd.symm.trans (Category.assoc _ _ _).symm
  let f : D.specialFibre.X ⟶ Y.X := Over.homMk (eD.inv ≫ f₀ ≫ eY.hom) (by
    calc
      _ = eD.inv ≫ (f₀ ≫ eY.hom ≫ Y.X.hom) := by simp only [Category.assoc]
      _ = _ := (congrArg (eD.inv ≫ ·) hw).trans (Iso.inv_hom_id_assoc _ _))
  have hs : Smooth f₀ := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (blowupResidue_smooth hr I hI))
  have hc : GeometricallyConnected f₀ := blowupResidue_geometricallyConnected hr I hI
  have hprop (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (h : P f₀) : P f.left := by
    change P (eD.inv ≫ f₀ ≫ eY.hom)
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ h)
  exact dilatation_structure_of_specialFibre M hr j f hM hY (hprop @Smooth hs)
    (hprop @GeometricallyConnected hc)

/-- The structural assertions for dilatations and all positive congruence models. -/
theorem dilatationStructure : DilatationStructureStatement.{u} :=
  ⟨smoothDilatation, smoothCongruenceModels_of_smoothDilatation smoothDilatation⟩

end Langlands.GroupScheme.IntegralModel
