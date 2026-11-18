import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus

/-! # Etale torus conjugacy retaining a fixed integral coordinate matrix -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {k : Type u} [Field k] {I J : Type u}
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The covariant integral character-coordinate equivalence of an actual
field torus isomorphism; its inverse is the ordinary character pullback. -/
def fieldTorusCoordinateEquiv
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) : (I → ℤ) ≃ₗ[ℤ] (J → ℤ) :=
  LinearEquiv.ofLinearMap (characterMap J I c.inv) (characterMap I J c.hom)
    (by rw [← characterMap_comp, c.inv_hom_id, characterMap_id])
    (by rw [← characterMap_comp, c.hom_inv_id, characterMap_id])

/-- Extending the field torus isomorphism is exactly the exponent isomorphism
for this one fixed integral matrix, over every base scheme. -/
theorem fieldIsoExtension_eq_coordinateIso (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) :
    fieldIsoExtension k I J S c =
      LocalSplitCell.exponentEquivGroupIso S (fieldTorusCoordinateEquiv c) := by
  apply Iso.ext
  rfl

variable {R : CommRingCat.{u}}

/-- On an affine etale neighborhood through each base point, two specified
maximal split tori are conjugate through one constant integral coordinate matrix. -/
theorem exists_etale_coordinateConjugacy
    (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec R) I ⟶ G) (j : splitTorus (Spec R) J ⟶ G)
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    (hj : IsFibrewiseMaximalTorus (T := commGroupScheme _ J) j) (s : Spec R) :
    ∃ (R' : CommRingCat.{u}) (b : Spec R' ⟶ Spec R), Etale b ∧ s ∈ Set.range b ∧
      ∃ (E : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
        (g : Over.mk (𝟙 (Spec R')) ⟶ ((GroupScheme.baseChange b).obj G).X),
        ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
            (((GroupScheme.baseChange b).obj G).innerIso g).hom =
          CommGroupScheme.groupHom (exponentEquivIso (Spec R') E).hom ≫
            ((baseChangeIso b J).inv ≫ (GroupScheme.baseChange b).map j) := by
  let k := AlgebraicClosure ((Spec R).residueField s)
  let b : Spec (CommRingCat.of k) ⟶ Spec R := geometricPoint (Spec R) s
  let GK := (GroupScheme.baseChange b).obj G
  let : Smooth GK.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))
  let : IsAffineHom GK.X.hom := inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom b))
  let iK : splitTorus (Spec (CommRingCat.of k)) I ⟶ GK :=
    (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i
  let jK : splitTorus (Spec (CommRingCat.of k)) J ⟶ GK :=
    (baseChangeIso b J).inv ≫ (GroupScheme.baseChange b).map j
  have hiK : IsMaximalTorus (T := commGroupScheme _ I) iK :=
    IsMaximalTorus.iso_comp (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ I))
      (T' := commGroupScheme _ I) (baseChangeIso b I).symm (hi.fieldPoint b)
  have hjK : IsMaximalTorus (T := commGroupScheme _ J) jK :=
    IsMaximalTorus.iso_comp (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ J))
      (T' := commGroupScheme _ J) (baseChangeIso b J).symm (hj.fieldPoint b)
  obtain ⟨g, c, hc, hg⟩ := maximalTorusConjugacy_in_identity GK
    (T := commGroupScheme _ I) (T' := commGroupScheme _ J) iK jK hiK hjK
  let t := fieldIsoExtension k I J (Spec R) c
  let E := fieldTorusCoordinateEquiv c
  have he : (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map t.hom ≫
      (baseChangeIso b J).hom = c.hom := fieldIsoExtension_baseChange k I J (Spec R) c b
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (t.hom ≫ j)) ((GroupScheme.baseChange b).map i) g := by
    apply (PointwiseSchemeAction.isTransporter_iff_innerIso _ _ g).mpr
    rw [Functor.map_comp]
    apply (cancel_epi (baseChangeIso b I).inv).mp
    calc
      _ = c.hom ≫ ((baseChangeIso b J).inv ≫ (GroupScheme.baseChange b).map j) := by
        simpa only [iK, jK, Category.assoc] using hc
      _ = _ := by rw [← he]; simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hb : b default = s := by
    simpa only [Subsingleton.elim (default : Spec (CommRingCat.of k))
      (IsLocalRing.closedPoint k)] using geometricPoint_closedPoint s
  let d := PointwiseSchemeAction.etaleIdentityTransporterOfSplitTorus
    (t.hom ≫ j) i inferInstance s b hb g ht hg
  refine ⟨d.neighbourhoodRing, d.projection, d.etale, d.mem_range, E,
    d.baseChangedSection, ?_⟩
  have hd := (PointwiseSchemeAction.isTransporter_iff_innerIso _ _
    d.baseChangedSection).mp d.baseChangedSection_isTransporter
  change (GroupScheme.baseChange d.projection).map i ≫
    (((GroupScheme.baseChange d.projection).obj G).innerIso d.baseChangedSection).hom =
      (GroupScheme.baseChange d.projection).map (t.hom ≫ j) at hd
  rw [Category.assoc, hd, Functor.map_comp]
  change (baseChangeIso d.projection I).inv ≫
    (GroupScheme.baseChange d.projection).map
      (CommGroupScheme.groupHom (exponentEquivIso (Spec R) E).hom) ≫
    (GroupScheme.baseChange d.projection).map j = _
  rw [baseChange_groupHom_exponentEquivIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Actual affine etale neighborhood data with a conjugator and its one fixed
integral torus-coordinate matrix. -/
structure EtaleCoordinateConjugacyData
    (G : GroupScheme (Spec R))
    (i : splitTorus (Spec R) I ⟶ G) (j : splitTorus (Spec R) J ⟶ G) (s : Spec R) where
  ring : CommRingCat.{u}
  projection : Spec ring ⟶ Spec R
  etale : Etale projection
  mem_range : s ∈ Set.range projection
  coordinateMap : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)
  conjugator : Over.mk (𝟙 (Spec ring)) ⟶ ((GroupScheme.baseChange projection).obj G).X
  square : ((baseChangeIso projection I).inv ≫ (GroupScheme.baseChange projection).map i) ≫
      (((GroupScheme.baseChange projection).obj G).innerIso conjugator).hom =
    CommGroupScheme.groupHom (exponentEquivIso (Spec ring) coordinateMap).hom ≫
      ((baseChangeIso projection J).inv ≫ (GroupScheme.baseChange projection).map j)

/-- Choose the proved actual affine etale coordinate conjugacy through a given
base point; existence of a constant-matrix conjugator is not an input. -/
def etaleCoordinateConjugacyAt
    (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec R) I ⟶ G) (j : splitTorus (Spec R) J ⟶ G)
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    (hj : IsFibrewiseMaximalTorus (T := commGroupScheme _ J) j) (s : Spec R) :
    EtaleCoordinateConjugacyData G i j s := Classical.choice <| by
  obtain ⟨R', b, hb, hs, E, g, hg⟩ := exists_etale_coordinateConjugacy G i j hi hj s
  exact ⟨⟨R', b, hb, hs, E, g, hg⟩⟩

end Langlands.GroupScheme.splitTorus
