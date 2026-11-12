import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportStatement
import Langlands.GroupScheme.Rational.AffineWeilParabolicElementaryStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Reduction of Weil elementary-subgroup comparison to diagram transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Transport of actual diagrams identifies the generator sets under the
published rational-point equivalence, before taking subgroup closures. -/
theorem affineWeil_parabolicUnipotentPointSet_image
    (h : AffineWeilParabolicRadicalTransportStatement.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (G : GroupScheme (Spec (CommRingCat.of K)))
    (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    (AffineWeil.rationalPointsEquiv k K G) ''
        parabolicUnipotentPointSet (AffineWeil.groupScheme k K G) =
      parabolicUnipotentPointSet G := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hG.smooth
  obtain ⟨hpres, hdesc⟩ := h k K G hG
  ext x
  constructor
  · rintro ⟨y, ⟨P, U, p, r, hp, hr, z, rfl⟩, rfl⟩
    obtain ⟨P', U', aP, lP, aU, lU, p', r', hp', hr', eP, eU, hep, her⟩ :=
      hdesc P U p r hp hr
    let := aP
    let := lP
    let := aU
    let := lU
    have hcomp : eU.hom ≫ AffineWeil.map k K (r' ≫ p') = r ≫ p := by
      rw [AffineWeil.map_comp, ← Category.assoc, her, Category.assoc, hep]
    refine ⟨P', U', p', r', hp', hr',
      AffineWeil.rationalPointsEquiv k K U' (rationalPoints.map eU.hom z), ?_⟩
    rw [← AffineWeil.rationalPointsEquiv_map]
    congr 1
    change (z ≫ eU.hom.hom.hom) ≫
      (AffineWeil.map k K (r' ≫ p')).hom.hom = z ≫ (r ≫ p).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hcomp]
  · rintro ⟨P, U, p, r, hp, hr, z, rfl⟩
    let := hp.isClosedSubgroup.isAffineHom
    let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
    let := hp.smooth
    let := hr.1.isClosedSubgroup.isAffineHom
    let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
    let := hr.1.smooth
    obtain ⟨hpW, hrW⟩ := hpres P U p r hp hr
    refine ⟨rationalPoints.map (AffineWeil.map k K r ≫ AffineWeil.map k K p)
      ((AffineWeil.rationalPointsEquiv k K U).symm z),
      ⟨AffineWeil.groupScheme k K P, AffineWeil.groupScheme k K U,
        AffineWeil.map k K p, AffineWeil.map k K r, hpW, hrW, _, rfl⟩, ?_⟩
    rw [← AffineWeil.map_comp, AffineWeil.rationalPointsEquiv_map,
      MulEquiv.apply_symm_apply]

/-- The all-test parabolic-radical correspondence suffices for the exact
published elementary-subgroup comparison, with no extra field hypothesis. -/
theorem affineWeilParabolicElementarySubgroup_of_radicalTransport
    (h : AffineWeilParabolicRadicalTransportStatement.{u}) :
    AffineWeilParabolicElementarySubgroupStatement.{u} := by
  intro k K _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hG.smooth
  change (Subgroup.closure _).map _ = Subgroup.closure _
  rw [MonoidHom.map_closure]
  exact congrArg Subgroup.closure
    (affineWeil_parabolicUnipotentPointSet_image h k K G hG)

end Langlands.GroupScheme
