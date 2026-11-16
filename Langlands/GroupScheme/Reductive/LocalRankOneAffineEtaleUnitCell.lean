import Langlands.GroupScheme.Reductive.LocalRankOnePointedUnitCell

/-! # Affine pointed etale normalizers with unit cell coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace PointedEtaleNormalizerData

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
  {G : GroupScheme (Spec R)} {i : T.toGrp ⟶ G} {σ : T ≅ T} {s : Spec R}
  {n₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X}
  (d : PointedEtaleNormalizerData i σ s n₀)

/-- Regard the pointed section as an actual point over the original base. -/
def pointMap : Over.mk d.projection ⟶ G.X :=
  (Over.homMk (𝟙 _) (by simp) : Over.mk d.projection ⟶
      (Over.map d.projection).obj (Over.mk (𝟙 d.neighbourhood))) ≫
    GroupScheme.baseChangePointsEquiv d.projection G _ d.sectionPoint

/-- The original-base point retains the prescribed action on every test. -/
theorem pointMap_isTransporter : PointwiseSchemeAction.IsTransporter
    (CommGroupScheme.groupHom σ.hom ≫ i) i d.pointMap := by
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange d.projection).map (CommGroupScheme.groupHom σ.hom ≫ i))
      ((GroupScheme.baseChange d.projection).map i) d.sectionPoint := by
    rw [Functor.map_comp]
    exact d.isNormalizing.isTransporter
  exact (ht.baseChangePointsEquiv d.projection).restrict _

/-- The original-base point recovers exactly the supplied residue normalizer. -/
theorem pointMap_recovers : d.residuePoint ≫ d.pointMap.left = n₀.left := by
  change d.residuePoint ≫ (𝟙 _ ≫
    (d.sectionPoint.left ≫ Limits.pullback.fst G.X.hom d.projection)) = n₀.left
  simpa only [Category.id_comp] using d.recovers

end PointedEtaleNormalizerData

namespace RingRootCell

variable {R : Type u} [CommRing R] (D : CellData R)
  (σ : D.T ≅ D.T) (s : Spec (CommRingCat.of R))
  (n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶ D.G.X)

/-- Actual affine etale normalizer coordinates retaining a specified residue point. -/
structure AffineEtaleUnitCellData where
  ring : CommRingCat.{u}
  projection : Spec ring ⟶ Spec (CommRingCat.of R)
  etale : Etale projection
  residuePoint : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec ring
  residue_over : residuePoint ≫ projection = (Spec (CommRingCat.of R)).fromSpecResidueField s
  normalizer : Over.mk projection ⟶ D.G.X
  isTransporter : PointwiseSchemeAction.IsTransporter
    (CommGroupScheme.groupHom σ.hom ≫ D.i) D.i normalizer
  recovers : residuePoint ≫ normalizer.left = n₀.left
  beta : Γ(Spec ring, ⊤)
  torus : Over.mk projection ⟶ D.T.X
  delta : Γ(Spec ring, ⊤)
  unit_beta : IsUnit beta
  unit_delta : IsUnit delta
  factorization : D.A 1 * normalizer = D.cellPt beta torus delta

variable {D σ s}

/-- Shrink a pointed normalizer lift so its residue unit coordinates extend
as unit coordinates over an actual affine etale neighbourhood. -/
def PointedEtaleUnitCellData.affineEtaleUnitCell
    (d : PointedEtaleUnitCellData D σ s) :
    AffineEtaleUnitCellData D σ s d.residueNormalizer := Classical.choice <| by
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk d.lift.projection
  let g : Z ⟶ D.G.X := D.A 1 * d.lift.pointMap
  let c : Over.mk (d.lift.residuePoint ≫ d.lift.projection) ⟶
      Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ (Spec (CommRingCat.of R)).fromSpecResidueField s =
        d.lift.residuePoint ≫ d.lift.projection
      rw [Category.id_comp, d.lift.residue_over])
  have hn : (Over.homMk d.lift.residuePoint rfl :
      Over.mk (d.lift.residuePoint ≫ d.lift.projection) ⟶ Z) ≫ d.lift.pointMap =
        c ≫ d.residueNormalizer := by
    apply Over.OverMorphism.ext
    change d.lift.residuePoint ≫ d.lift.pointMap.left = 𝟙 _ ≫ d.residueNormalizer.left
    rw [Category.id_comp, d.lift.pointMap_recovers]
  have hg : (Over.homMk d.lift.residuePoint rfl :
      Over.mk (d.lift.residuePoint ≫ d.lift.projection) ⟶ Z) ≫ g =
        D.cellPt d.beta (c ≫ d.torus) d.delta := by
    change _ ≫ (D.A 1 * d.lift.pointMap) = _
    rw [MonObj.comp_mul, D.comp_A, map_one, hn]
    have h := congrArg (fun v => c ≫ v) d.factorization
    have hc (x : Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)) :
        c.left.appTop x = x := rfl
    simpa only [MonObj.comp_mul, D.comp_A, D.comp_cellPt, map_one, hc] using h
  let E := LocalRankOneUnitCell.affineUnitCell D g d.lift.residuePoint
    d.beta (c ≫ d.torus) d.delta d.unit_beta d.unit_delta hg
  let W : Over (Spec (CommRingCat.of R)) := Over.mk (E.inclusion ≫ d.lift.projection)
  let j : W ⟶ Z := Over.homMk E.inclusion rfl
  let : IsOpenImmersion E.inclusion := E.openImmersion
  let : Etale d.lift.projection := d.lift.etale
  refine ⟨{ ring := E.ring, projection := E.inclusion ≫ d.lift.projection
            etale := inferInstance, residuePoint := E.point
            residue_over := ?_, normalizer := j ≫ d.lift.pointMap
            isTransporter := d.lift.pointMap_isTransporter.restrict j
            recovers := ?_, beta := E.beta, torus := E.torus, delta := E.delta
            unit_beta := E.unit_beta, unit_delta := E.unit_delta
            factorization := ?_ }⟩
  · rw [← Category.assoc, E.point_comp, d.lift.residue_over]
  · change E.point ≫ (E.inclusion ≫ d.lift.pointMap.left) = d.residueNormalizer.left
    rw [← Category.assoc, E.point_comp, d.lift.pointMap_recovers]
  · have h := E.factorization
    change j ≫ (D.A 1 * d.lift.pointMap) = _ at h
    rw [MonObj.comp_mul, D.comp_A, map_one] at h
    exact h

end RingRootCell

end Langlands.GroupScheme
