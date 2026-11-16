import Langlands.GroupScheme.Reductive.RankOneRingDualBaseChange
import Langlands.GroupScheme.Reductive.LocalRankOneAffineWeylData

/-! # Units from actual affine etale rank-one Weyl data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell.AffineEtaleUnitCellData

variable {R : Type u} [CommRing R] [IsLocalRing R] {D : CellData R}
  {σ : D.T ≅ D.T}
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)) ⟶ D.G.X}
  (E : AffineEtaleUnitCellData D σ (IsLocalRing.closedPoint R) n₀)

/-- The retained point over the closed point reflects coefficient units. -/
theorem isUnit_of_coefficientImage (c : R) :
    let := E.coefficientAlgebra
    IsUnit (algebraMap R E.ring c) → IsUnit c := by
  let := E.coefficientAlgebra
  change IsUnit (algebraMap R E.ring c) → IsUnit c
  let k := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)
  let ρ : E.ring →+* k := (Spec.preimage E.residuePoint).hom
  let τ : R →+* k := ρ.comp (algebraMap R E.ring)
  have hτ : Spec.map (CommRingCat.ofHom τ) =
      (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) := by
    change Spec.map (CommRingCat.ofHom
      ((Spec.preimage E.residuePoint).hom.comp (algebraMap R E.ring))) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change Spec.map (Spec.preimage E.residuePoint) ≫ algebraBaseMap R E.ring = _
    rw [Spec.map_preimage, E.coefficientAlgebra_baseMap, E.residue_over]
  have hlocal : IsLocalHom τ :=
    (IsLocalRing.isLocalHom_iff_comap_closedPoint τ).mpr (by
      change (Spec.map (CommRingCat.ofHom τ)) (IsLocalRing.closedPoint k) = _
      rw [hτ]
      exact Scheme.fromSpecResidueField_apply _ _)
  let := hlocal
  intro hc
  exact isUnit_of_map_unit τ c (hc.map ρ)

/-- The unique coefficient unit recovered from its unit image. -/
def coefficientUnit (c : R)
    (hc : letI := E.coefficientAlgebra
      IsUnit (algebraMap R E.ring c)) : Rˣ :=
  (E.isUnit_of_coefficientImage c hc).unit

/-- The recovered unit has exactly the original coefficient as its value. -/
theorem coefficientUnit_val (c : R)
    (hc : letI := E.coefficientAlgebra
      IsUnit (algebraMap R E.ring c)) :
    (E.coefficientUnit c hc : R) = c :=
  (E.isUnit_of_coefficientImage c hc).unit_spec

/-- An etale neighbourhood retaining a point above the closed point of a
local base is surjective on the entire base spectrum. -/
theorem projection_surjective : Function.Surjective E.projection := by
  let := E.etale
  have hs : IsLocalRing.closedPoint R ∈ Set.range E.projection := by
    refine ⟨E.residuePoint (IsLocalRing.closedPoint _), ?_⟩
    change (E.residuePoint ≫ E.projection) (IsLocalRing.closedPoint _) = _
    rw [E.residue_over, Scheme.fromSpecResidueField_apply]
  have hopen : IsOpen (Set.range E.projection) := E.projection.isOpenMap.isOpen_range
  intro p
  exact (IsLocalRing.specializes_closedPoint p).mem_open hopen hs

end RingRootCell.AffineEtaleUnitCellData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange LocalWeylNormalization

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)
  {s : Spec (CommRingCat.of R)}
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
    (groupScheme I G i mu).X}
  (E : RingRootCell.AffineEtaleUnitCellData
    (corootCellData i mu hG hmax hP a ha hmu hp hm)
    (LocalRankOneWeylData.corootReflectionIso hP a) s n₀)

/-- The dual coefficient of the original actual centralizer cell maps
exactly to the inverse beta unit of its affine etale Weyl data. -/
theorem algebraMap_normalizationScalar (hi : IsClosedSubgroup i)
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : (corootCellData i mu hG hmax hP a ha hmu hp hm).A 1 *
        (corootCellData i mu hG hmax hP a ha hmu hp hm).B (epsSec R) =
      (corootCellData i mu hG hmax hP a ha hmu hp hm).cellPt y t x) :
    let := E.coefficientAlgebra
    algebraMap R E.ring (RingRootCell.DualCell.normalizationScalar x) =
      (↑(affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).betaUnit⁻¹ : E.ring) := by
  let := E.coefficientAlgebra
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let C := groupScheme I G i mu
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange (algebraBaseMap R E.ring)).obj C).X.hom)
    exact inferInstanceAs (IsAffineHom
      (Limits.pullback.snd C.X.hom (algebraBaseMap R E.ring)))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  exact LocalRankOneCell.algebraMap_normalizationScalar
    (torusHom I G i mu) (P.root a)
    (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))
    (rootLift i mu hp ha)
    (isRootParametrization_rootLift i mu hm _)
    (isRootParametrization_rootLift i mu hp ha)
    D.open_cell E.ring W rfl hx

omit E in
/-- The normalization coefficient is a unit over the original arbitrary
local ring whenever the affine etale neighbourhood retains a closed point. -/
theorem isUnit_normalizationScalar (hi : IsClosedSubgroup i)
    {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)) ⟶ (groupScheme I G i mu).X}
    (E : RingRootCell.AffineEtaleUnitCellData
      (corootCellData i mu hG hmax hP a ha hmu hp hm)
      (LocalRankOneWeylData.corootReflectionIso hP a) (IsLocalRing.closedPoint R) n₀)
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : (corootCellData i mu hG hmax hP a ha hmu hp hm).A 1 *
        (corootCellData i mu hG hmax hP a ha hmu hp hm).B (epsSec R) =
      (corootCellData i mu hG hmax hP a ha hmu hp hm).cellPt y t x) :
    IsUnit (RingRootCell.DualCell.normalizationScalar x) := by
  apply E.isUnit_of_coefficientImage
  let := E.coefficientAlgebra
  rw [algebraMap_normalizationScalar i mu hG hmax hP a ha hmu hp hm E hi hx]
  exact Units.isUnit _

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
