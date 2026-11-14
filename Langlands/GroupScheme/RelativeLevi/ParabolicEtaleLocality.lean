import Langlands.GroupScheme.RelativeLevi.ParabolicLocality
import Langlands.GroupScheme.Descent.GaloisInvariantParabolics
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Relative parabolicity is detected by a surjective étale base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {P G : GroupScheme S}

/-- Relative parabolicity in a reductive ambient group is detected by every
surjective étale change of base. -/
theorem IsRelativeParabolicSubgroup.of_etale_surjective (hG : IsReductive G)
    (b : S' ⟶ S) [Etale b] [Surjective b] (j : P ⟶ G)
    (h : IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map j)) :
    IsRelativeParabolicSubgroup j := by
  let : MorphismProperty.DescendsAlong (@Smooth.{u}) (@Etale.{u} ⊓ @Surjective.{u}) :=
    Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent.descendsAlong_etale_surjective _
  have hs : Smooth P.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @Smooth) (Q := @Etale ⊓ @Surjective)
      (f := P.X.hom) (g := b) ⟨inferInstance, inferInstance⟩ h.smooth
  have ha : IsAffineHom P.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @IsAffineHom) (Q := @Etale ⊓ @Surjective)
      (f := P.X.hom) (g := b) ⟨inferInstance, inferInstance⟩ h.isAffineHom
  have hm : Mono j.hom.hom :=
    (Over.pullback b).mono_of_mono_map h.mono
  let : IsAffineHom P.X.hom := ha
  let : IsAffineHom G.X.hom := hG.isAffineHom
  refine ⟨hs, ha, hm, fun s => ?_⟩
  obtain ⟨s', rfl⟩ := b.surjective s
  let k := S.residueField (b s')
  let K := S'.residueField s'
  let φ : CommRingCat.of k ⟶ CommRingCat.of K := b.residueFieldMap s'
  let : Algebra k K := φ.hom.toAlgebra
  have : Algebra.IsSeparable k K := inferInstance
  have : Algebra.IsAlgebraic k K := inferInstance
  let r : Spec (CommRingCat.of k) ⟶ S := S.fromSpecResidueField (b s')
  let r' : Spec (CommRingCat.of K) ⟶ S' := S'.fromSpecResidueField s'
  let q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map φ
  have hq : q ≫ r = r' ≫ b := b.SpecMap_residueFieldMap_fromSpecResidueField s'
  let eP := Descent.pullbackComparison b r' (r' ≫ b) rfl P
  let eG := Descent.pullbackComparison b r' (r' ≫ b) rfl G
  have htotal : IsParabolicSubgroup ((GroupScheme.baseChange (r' ≫ b)).map j) := by
    have ht := ((h.residueFiber s').iso_comp eP.symm).comp_iso eG
    change IsParabolicSubgroup ((eP.inv ≫ (GroupScheme.baseChange r').map
      ((GroupScheme.baseChange b).map j)) ≫ eG.hom) at ht
    have he : eP.inv ≫ (GroupScheme.baseChange r').map
        ((GroupScheme.baseChange b).map j) ≫ eG.hom =
          (GroupScheme.baseChange (r' ≫ b)).map j := by
      rw [Descent.pullbackComparison_naturality, Iso.inv_hom_id_assoc]
    simpa only [Iso.symm_hom, Category.assoc, he] using ht
  let dP := Descent.pullbackComparison r q (r' ≫ b) hq P
  let dG := Descent.pullbackComparison r q (r' ≫ b) hq G
  have hiter : IsParabolicSubgroup
      ((GroupScheme.baseChange q).map ((GroupScheme.baseChange r).map j)) := by
    have ht := (htotal.iso_comp dP).comp_iso dG.symm
    have he : dP.hom ≫ (GroupScheme.baseChange (r' ≫ b)).map j ≫ dG.inv =
        (GroupScheme.baseChange q).map ((GroupScheme.baseChange r).map j) := by
      rw [← Category.assoc, ← Descent.pullbackComparison_naturality,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Iso.symm_hom, Category.assoc, he] using ht
  have : IsAffine ((GroupScheme.baseChange r).obj P).X.left := by
    change IsAffine (pullback P.X.hom r)
    infer_instance
  have : IsAffine ((GroupScheme.baseChange r).obj G).X.left := by
    change IsAffine (pullback G.X.hom r)
    infer_instance
  have : Flat q := (fieldExtension_fpqc k K).2.1
  have : Surjective q := (fieldExtension_fpqc k K).1
  have hc : IsClosedSubgroup ((GroupScheme.baseChange r).map j) :=
    IsClosedSubgroup.of_baseChange_of_isAffine q hiter.isClosedSubgroup
  exact hiter.of_baseChange_of_algebraicExtension hc

/-- Relative parabolicity in a reductive group is equivalent to its pullback
along a surjective étale morphism. -/
theorem isRelativeParabolicSubgroup_iff_etale_surjective (hG : IsReductive G)
    (b : S' ⟶ S) [Etale b] [Surjective b] (j : P ⟶ G) :
    IsRelativeParabolicSubgroup j ↔
      IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map j) :=
  ⟨fun hj => hj.baseChange hG b,
    IsRelativeParabolicSubgroup.of_etale_surjective hG b j⟩

namespace ParabolicSubgroupModuli

/-- Construct the actual parabolic subgroup defined by an inclusion whose
pullback along a surjective étale cover is relatively parabolic. -/
def ofEtaleSurjective (hG : IsReductive G)
    (b : S' ⟶ S) [Etale b] [Surjective b] (j : P ⟶ G)
    (h : IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map j)) :
    ParabolicSubgroup G :=
  ⟨SubgroupFunctor.range j,
    isParabolic_range j (IsRelativeParabolicSubgroup.of_etale_surjective hG b j h)⟩

@[simp]
theorem ofEtaleSurjective_val (hG : IsReductive G)
    (b : S' ⟶ S) [Etale b] [Surjective b] (j : P ⟶ G)
    (h : IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map j)) :
    (ofEtaleSurjective hG b j h).val = SubgroupFunctor.range j := rfl

/-- The constructed subgroup recovers the prescribed inclusion after base change. -/
theorem ofEtaleSurjective_baseChange (hG : IsReductive G)
    (b : S' ⟶ S) [Etale b] [Surjective b] (j : P ⟶ G)
    (h : IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map j)) :
    (ofEtaleSurjective hG b j h).val.baseChange b =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j) :=
  (SubgroupFunctor.range_baseChangeHom b j).symm

end ParabolicSubgroupModuli

end Langlands.GroupScheme
