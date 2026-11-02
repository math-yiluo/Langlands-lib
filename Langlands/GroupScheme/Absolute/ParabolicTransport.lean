import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Parabolic subgroup presentations and base change of ranges -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} {H G : GroupScheme S}

/-- Base change of the range is the range of the base-changed homomorphism. -/
theorem range_baseChange (b : S' ⟶ S) (i : H ⟶ G) :
    (range i).baseChange b = range ((GroupScheme.baseChange b).map i) := by
  apply ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_baseChange, mem_range, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(baseChangePointsEquiv b H T).symm y, ?_⟩
    apply (baseChangePointsEquiv b G T).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    exact ⟨baseChangePointsEquiv b H T y, (baseChangePointsEquiv_comp b i T y).symm⟩

/-- The homomorphism between monic subgroup presentations induced by inclusion of ranges. -/
def factorOfRangeLE {H' : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}
    [Mono i.hom.hom] [Mono i'.hom.hom] (h : range i ≤ range i') : H ⟶ H' := by
  let hi : (range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hi' : (range i').IsRepresentedBy i' := ⟨inferInstance, rfl⟩
  let φ : ∀ T : Over S, (range i).carrier T →* (range i').carrier T :=
    fun T => Subgroup.inclusion (h T)
  exact hi.lift hi' φ (fun _ _ => rfl)

/-- The induced homomorphism commutes with the subgroup inclusions. -/
theorem factorOfRangeLE_comp {H' : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}
    [Mono i.hom.hom] [Mono i'.hom.hom] (h : range i ≤ range i') :
    factorOfRangeLE h ≫ i' = i := by
  exact IsRepresentedBy.lift_comp_eq
    (show (range i).IsRepresentedBy i from ⟨inferInstance, rfl⟩)
    (show (range i').IsRepresentedBy i' from ⟨inferInstance, rfl⟩)
    (fun T => Subgroup.inclusion (h T)) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Inclusion of two represented subgroup functors gives a factorization of their inclusions. -/
theorem exists_factor_of_range_le {H' : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}
    [Mono i.hom.hom] [Mono i'.hom.hom] (h : range i ≤ range i') :
    ∃ f : H ⟶ H', f ≫ i' = i :=
  ⟨factorOfRangeLE h, factorOfRangeLE_comp h⟩

/-- A factorization of subgroup inclusions implies inclusion of ranges on every test scheme. -/
theorem range_le_of_factor {H' : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}
    (f : H ⟶ H') (hf : f ≫ i' = i) : range i ≤ range i' := by
  rintro T x ⟨y, rfl⟩
  change T ⟶ H.X at y
  refine ⟨y ≫ f.hom.hom, ?_⟩
  change (y ≫ f.hom.hom) ≫ i'.hom.hom = y ≫ i.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hf]

end SubgroupFunctor

variable {k : Type u} [Field k]
variable {P P' G : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}

/-- A change of the source presentation of a parabolic subgroup preserves parabolicity. -/
theorem IsParabolicSubgroup.iso_comp (hi : IsParabolicSubgroup i) (e : P' ≅ P) :
    IsParabolicSubgroup (e.hom ≫ i) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : Smooth P.X.hom := hi.smooth
  refine ⟨?_, ?_, ?_⟩
  · change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
    let F := GroupScheme.baseChange (toAlgebraicClosure k)
    refine ⟨B, j, f ≫ F.map e.inv, hj, ?_⟩
    change (f ≫ F.map e.inv) ≫ F.map (e.hom ≫ i) = j
    have he : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
      rw [← F.map_comp, e.inv_hom_id, F.map_id]
    rw [F.map_comp, Category.assoc, ← Category.assoc (F.map e.inv), he,
      Category.id_comp]
    exact hf

/-- Parabolicity depends only on the all-test subgroup functor of a closed subgroup. -/
theorem IsParabolicSubgroup.of_range_eq (hi : IsParabolicSubgroup i) {i' : P' ⟶ G}
    (hi' : IsClosedSubgroup i') (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsParabolicSubgroup i' := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' := ⟨inferInstance, h.symm⟩
  let e := hr.isoOfIsRepresentedBy hr'
  have he : e.hom ≫ i' = i := hr.isoOfIsRepresentedBy_hom_comp hr'
  have he' : e.inv ≫ i = i' := by
    rw [← he, Iso.inv_hom_id_assoc]
  have htransport := hi.iso_comp e.symm
  change IsParabolicSubgroup (e.inv ≫ i) at htransport
  rwa [he'] at htransport

/-- Two closed subgroup presentations of the same subgroup functor are parabolic together. -/
theorem isParabolicSubgroup_iff_of_range_eq {i' : P' ⟶ G}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsParabolicSubgroup i ↔ IsParabolicSubgroup i' :=
  ⟨fun hp => hp.of_range_eq hi' h, fun hp => hp.of_range_eq hi h.symm⟩

end Langlands.GroupScheme
