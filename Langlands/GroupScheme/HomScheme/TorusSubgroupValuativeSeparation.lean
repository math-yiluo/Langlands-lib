import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Torus.RelativeGeometry

/-! # Restriction of torus subgroups to schematically dominant bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

private theorem range_le_of_dominant_baseChange {B : Scheme.{u}} (b : B ⟶ S)
    [QuasiCompact b] [IsSchemeTheoreticallyDominant b]
    {H K : GroupScheme S} [Flat H.X.hom] (i : H ⟶ G) {j : K ⟶ G}
    (hj : IsClosedSubgroup j) (h : (range i).baseChange b ≤ (range j).baseChange b) :
    range i ≤ range j := by
  let i' := (baseChange b).map i
  have hi' : i'.hom.hom ∈ ((range i).baseChange b).carrier ((baseChange b).obj H).X := by
    rw [← range_baseChangeHom]
    exact mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  have hc := h _ hi'
  rw [mem_baseChange, hj.mem_range_iff_ker_le _, baseChangePointsEquiv_left] at hc
  have hw : i'.hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom b ≫ i.hom.hom.left := pullback.lift_fst _ _ _
  rw [hw, Scheme.Hom.ker_comp, (pullback.fst H.X.hom b).ker_eq_bot,
    Scheme.IdealSheafData.map_bot] at hc
  intro T x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  exact (hj.mem_range_iff_ker_le _).mpr (hc.trans (Scheme.Hom.le_ker_comp y.left _))

/-- Restriction of admissible subgroup functors along a quasi-compact
schematically dominant change of test scheme is an embedding. -/
def dominantRestrictionEmbedding {M T : Over S} (a : T ⟶ M)
    [QuasiCompact a.left] [IsSchemeTheoreticallyDominant a.left] :
    AdmissibleSubgroup ((baseChange M.hom).obj G) ↪
      AdmissibleSubgroup ((baseChange T.hom).obj G) where
  toFun := restrict a
  inj' := by
    intro F F' h
    let r := admissibleRepresentative F
    let r' := admissibleRepresentative F'
    let : Smooth r.group.X.hom := r.torus.smooth
    let : Smooth r'.group.X.hom := r'.torus.smooth
    have hEval : evaluate r.hom a = evaluate r'.hom a := congrArg Subtype.val h
    have hBase := (range_comp_iso_eq_iff ((baseChange a.left).map r.hom)
      ((baseChange a.left).map r'.hom)
      (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G)).mp hEval
    rw [range_baseChangeHom, range_baseChangeHom] at hBase
    apply Subtype.ext
    change F.val = F'.val
    rw [← r.represents.2, ← r'.represents.2]
    exact le_antisymm (range_le_of_dominant_baseChange a.left r.hom r'.closed hBase.le)
      (range_le_of_dominant_baseChange a.left r'.hom r.closed hBase.ge)

/-- The actual small torus-subgroup presheaf satisfies the valuative
separation condition in Murre's representability criterion. -/
theorem smallAdmissiblePresheaf_valuativeSeparation (G : GroupScheme S) :
    ValuativeSeparation (smallAdmissiblePresheaf G) := by
  intro V _ _ _ f F F' h
  let a := algebraOverBase f (FractionRing V)
  let : QuasiCompact a.left := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    infer_instance
  let : IsSchemeTheoreticallyDominant a.left :=
    isSchemeTheoreticallyDominant_specMap (IsFractionRing.injective V (FractionRing V))
  apply (smallAdmissibleEquiv G (Over.mk f)).injective
  apply (dominantRestrictionEmbedding a).injective
  change restrict a _ = restrict a _
  rw [← smallAdmissibleEquiv_map, ← smallAdmissibleEquiv_map, h]

end Langlands.GroupScheme.TorusSubgroupModuli
