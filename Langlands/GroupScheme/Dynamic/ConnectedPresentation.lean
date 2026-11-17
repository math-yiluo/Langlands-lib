import Langlands.GroupScheme.ConnectedMonoRigidity
import Langlands.GroupScheme.Dynamic.LocalContainment
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # A prescribed dynamic presentation over a connected base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

/-- A dynamic parabolic of a smooth geometrically connected affine group
over a connected base is the whole group if it is so on one field fibre. -/
theorem parabolic_eq_top_of_field_eq_top_of_connected
    {S : Scheme.{u}} [ConnectedSpace S] {H : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (χ : (Gm S).toGrp ⟶ H) (k : Type u) [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : parabolic (baseChangeCocharacter b χ) = ⊤) : parabolic χ = ⊤ := by
  obtain ⟨K, j, hjc, -, hj⟩ := (dynamicBaseRepresentability S H χ).1
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : Mono j.hom.hom := hj.1
  let : Smooth K.X.hom := (dynamicBaseSmoothConnected S H χ K j).2.1 hj |>.1
  let : GeometricallyConnected K.X.hom :=
    ((dynamicBaseSmoothConnected S H χ K j).2.1 hj).2 inferInstance
  let : IsAffineHom K.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hbj : IsIso ((baseChange b).map j) := by
    let hjb := hj.baseChange b
    have hr : SubgroupFunctor.range ((baseChange b).map j) = ⊤ := by
      rw [hjb.2, ← parabolic_baseChange]
      exact hb
    let : Mono ((baseChange b).map j).hom.hom := hjb.1
    let : IsIso ((baseChange b).map j).hom.hom :=
      DynamicContainment.isIso_of_range_eq_top _ hr
    exact TorusIsomorphismLocus.isIso_of_underlying _
  let : IsIso j := SmoothIsomorphismLocus.isIso_of_fieldIso_of_connected j k b hbj
  rw [← hj.2]
  ext U x
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  exact SubgroupFunctor.mem_range.mpr ⟨x ≫ inv j.hom.hom, by simp⟩

section Presentation

variable {S : Scheme.{u}} [ConnectedSpace S] {H G K : GroupScheme S}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
  (i : H ⟶ G) (hi : IsClosedSubgroup i) (χ : (Gm S).toGrp ⟶ H)
  (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
  (hb : SubgroupFunctor.range ((baseChange b).map i) =
    parabolic (baseChangeCocharacter b (χ ≫ i)))

include hi hb

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom] in
/-- The supplied subgroup lies in the prescribed ambient dynamic parabolic
globally once it equals that parabolic on one field fibre. -/
theorem range_le_parabolic_of_field_presentation :
    SubgroupFunctor.range i ≤ parabolic (χ ≫ i) := by
  have htop : parabolic (baseChangeCocharacter b χ) = ⊤ := by
    rw [parabolic_eq_comap_of_isClosedSubgroup (baseChangeCocharacter b χ)
      ((baseChange b).map i) (hi.baseChange b), ← baseChangeCocharacter_comp_hom, ← hb]
    ext U x
    refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
    rw [SubgroupFunctor.mem_comap]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  exact range_le_parabolic_comp_of_top i χ
    (parabolic_eq_top_of_field_eq_top_of_connected χ k b htop)

/-- A subgroup agreeing with a prescribed dynamic parabolic on one field
fibre is isomorphic to any actual representative of that parabolic globally. -/
theorem exists_parabolicIso_of_field_presentation (j : K ⟶ G)
    (hj : (parabolic (χ ≫ i)).IsRepresentedBy j) :
    ∃ e : H ≅ K, e.hom ≫ j = i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hjclosed : IsClosedSubgroup j := by
    obtain ⟨P, p, hpc, -, hp⟩ := (dynamicBaseRepresentability S G (χ ≫ i)).1
    rw [← hj.isoOfIsRepresentedBy_hom_comp hp]
    exact (IsClosedSubgroup.of_iso (hj.isoOfIsRepresentedBy hp)).comp hpc
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : Mono j.hom.hom := hj.1
  let : IsAffineHom K.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth K.X.hom := (dynamicBaseSmoothConnected S G (χ ≫ i) K j).2.1 hj |>.1
  let : GeometricallyConnected K.X.hom :=
    ((dynamicBaseSmoothConnected S G (χ ≫ i) K j).2.1 hj).2 inferInstance
  let f := hj.liftOfLE i (range_le_parabolic_of_field_presentation i hi χ k b hb)
  have hfac : f ≫ j = i := hj.liftOfLE_comp i _
  have : Mono (f.hom.hom ≫ j.hom.hom) := by
    change Mono (f ≫ j).hom.hom
    rw [hfac]
    infer_instance
  let : Mono f.hom.hom := mono_of_mono f.hom.hom j.hom.hom
  have hbf : IsIso ((baseChange b).map f) := by
    have hbj := hj.baseChange b
    rw [← parabolic_baseChange] at hbj
    let : IsClosedImmersion ((baseChange b).map i).hom.hom.left := hi.baseChange b
    have hbi : (parabolic (baseChangeCocharacter b (χ ≫ i))).IsRepresentedBy
        ((baseChange b).map i) :=
      ⟨Over.mono_of_mono_left _, hb⟩
    let e := hbi.isoOfIsRepresentedBy hbj
    have he : (baseChange b).map f = e.hom := by
      apply hbj.hom_ext
      rw [← Functor.map_comp, hfac]
      exact (hbi.isoOfIsRepresentedBy_hom_comp hbj).symm
    rw [he]
    infer_instance
  let : IsIso f := SmoothIsomorphismLocus.isIso_of_fieldIso_of_connected f k b hbf
  exact ⟨asIso f, hfac⟩

/-- Choose the global comparison with the actual prescribed dynamic
parabolic, retaining the original inclusion equation. -/
def parabolicIsoOfFieldPresentation (j : K ⟶ G)
    (hj : (parabolic (χ ≫ i)).IsRepresentedBy j) : H ≅ K :=
  (exists_parabolicIso_of_field_presentation i hi χ k b hb j hj).choose

/-- The constructed isomorphism carries the original subgroup inclusion
to the prescribed dynamic-parabolic inclusion. -/
theorem parabolicIsoOfFieldPresentation_hom_comp (j : K ⟶ G)
    (hj : (parabolic (χ ≫ i)).IsRepresentedBy j) :
    (parabolicIsoOfFieldPresentation i hi χ k b hb j hj).hom ≫ j = i :=
  (exists_parabolicIso_of_field_presentation i hi χ k b hb j hj).choose_spec

/-- Equality with one prescribed ambient dynamic parabolic propagates from
a single actual field fibre over a connected base. -/
theorem range_eq_parabolic_of_field_presentation :
    SubgroupFunctor.range i = parabolic (χ ≫ i) := by
  obtain ⟨K, j, -, -, hj⟩ := (dynamicBaseRepresentability S G (χ ≫ i)).1
  let e := parabolicIsoOfFieldPresentation i hi χ k b hb j hj
  have he : e.hom ≫ j = i := parabolicIsoOfFieldPresentation_hom_comp i hi χ k b hb j hj
  rw [← hj.2, ← he]
  exact SubgroupFunctor.range_iso_comp e j

end Presentation

end Langlands.GroupScheme.Dynamic
