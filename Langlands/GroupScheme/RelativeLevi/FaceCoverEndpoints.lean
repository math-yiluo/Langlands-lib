import Langlands.GroupScheme.RelativeLevi.FaceCoverTermMaps
import Langlands.GroupScheme.UnitSubgroup

/-! # The prescribed radical and the finite terminal face term -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open LocalSplitCell SubgroupFunctor

variable {S : Scheme.{u}} {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)

local instance endpointsAmbientAffine {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

variable (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

include hp hr in
omit [IsAffineHom G.X.hom] in
/-- The supplied radical retains a monic original composite into the ambient group. -/
theorem suppliedRadical_ambient_mono : Mono (r ≫ p).hom.hom := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  change Mono (r.hom.hom ≫ p.hom.hom)
  exact mono_comp' inferInstance hp.mono

include hG hp hr in
/-- The initial ORIGINAL chart term represents the supplied original radical pullback. -/
theorem localTermFunctor_zero_eq (a : D.chartCover.I₀) :
    D.localTermFunctor 0 a = range ((baseChange (D.chartCover.f a)).map (r ≫ p)) := by
  let C := (D.charts a.down).2
  let b := D.chartCover.f a
  let : Fintype C.coordinateType := C.coordinateFintype
  let : Fintype C.rootType := C.rootFintype
  let : IsAffine (D.chartCover.X a) := by
    change IsAffine (Spec C.ring)
    infer_instance
  let : IsAffine ((baseChange b).obj G).X.left :=
    isAffine_of_isAffineHom ((baseChange b).obj G).X.hom
  have hrep := isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi
    (hG.baseChange b) (AffineRegularBorel.cocharacter C.torus C.weight)
    C.represents ((baseChange b).map r) (hr.baseChange_parabolic hp hG b)
  rw [Functor.map_comp]
  exact C.chart.represented.2.trans hrep.2.symm

include hG hp hr in
/-- The first actual global term is the supplied radical with its ORIGINAL ambient map. -/
theorem termFunctor_zero_eq_range : D.termFunctor 0 = range (r ≫ p) := by
  let R := D.closedTermRepresentative r hG hp hr 0
  let : Mono R.hom.hom.hom := R.represents.1
  let : Mono (r ≫ p).hom.hom := suppliedRadical_ambient_mono r hp hr
  rw [← R.represents.2]
  apply (range_eq_iff_baseChange_etaleCover D.chartCover R.hom (r ≫ p)).mpr
  intro a
  rw [R.represents.2, D.termFunctor_baseChange r hG hp hr, ← range_baseChangeHom]
  exact D.localTermFunctor_zero_eq r hG hp hr a

/-- The prescribed supplied radical is the actual initial global term. -/
def globalTermZeroIso : D.globalTerm r hG hp hr 0 ≅ U :=
  (D.closedTermRepresentative r hG hp hr 0).represents.isoOfIsRepresentedBy
    ⟨suppliedRadical_ambient_mono r hp hr, (D.termFunctor_zero_eq_range r hG hp hr).symm⟩

/-- This identification preserves the original supplied radical inclusion. -/
theorem globalTermZeroIso_hom_comp :
    (D.globalTermZeroIso r hG hp hr).hom ≫ (r ≫ p) =
      D.globalTermInclusion r hG hp hr 0 :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The one finite bound makes every original local terminal range trivial on ALL tests. -/
theorem localTermFunctor_bound_eq_bot (a : D.chartCover.I₀) :
    D.localTermFunctor D.bound a = ⊥ := by
  let C := (D.charts a.down).2
  let : Fintype C.coordinateType := C.coordinateFintype
  let : Fintype C.rootType := C.rootFintype
  let : IsAffine ((baseChange C.projection).obj G).X.left :=
    isAffine_of_isAffineHom ((baseChange C.projection).obj G).X.hom
  have hw : ∀ α : C.rootType, C.chart.allRootWeight α < D.bound + 1 := by
    intro α
    by_cases hpos : C.chart.base.IsPos α
    · let k := C.chart.index.symm ⟨α, hpos⟩
      have hk : (C.chart.index k : C.rootType) = α :=
        congrArg Subtype.val (C.chart.index.apply_symm_apply ⟨α, hpos⟩)
      rw [← hk, C.chart.allRootWeight_index]
      exact Nat.lt_succ_of_le (D.weight_le_bound a.down k)
    · have hn := C.chart.faceHeight_nonpos_of_not_isPos α hpos
      have hz : C.chart.allRootWeight α = 0 := Int.toNat_of_nonpos hn
      rw [hz]
      exact Nat.zero_lt_succ _
  change range (C.termInclusion D.bound) = ⊥
  rw [C.range_termInclusion_eq_allRootSubgroup]
  apply SubgroupFunctor.ext
  intro T
  exact Langlands.GroupTheory.HeightFiltration.level_eq_bot _ _
    (fun k => hw (SplitParabolicFaceChart.allRootIndex C.rootType k))

include hG hp hr in
/-- The finite bound terminates the descended ambient subgroup on all scheme tests. -/
theorem termFunctor_bound_eq_bot : D.termFunctor D.bound = ⊥ := by
  apply (eq_iff_isRepresentedBy_baseChange_etaleCover D.chartCover
    (D.closedTermRepresentative r hG hp hr D.bound).represents
    (bot_isRepresentedBy_kernelUnit G)).mpr
  intro a
  rw [D.termFunctor_baseChange r hG hp hr, bot_baseChange]
  exact D.localTermFunctor_bound_eq_bot a

/-- The actual global terminal group has only its identity point on every scheme test. -/
theorem globalTerm_bound_range_id_eq_bot :
    range (𝟙 (D.globalTerm r hG hp hr D.bound)) = ⊥ := by
  let R := D.closedTermRepresentative r hG hp hr D.bound
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [bot_carrier, Subgroup.mem_bot]
  constructor
  · intro _
    have hx : x ≫ R.hom.hom.hom ∈ (D.termFunctor D.bound).carrier T :=
      (R.represents.pointsEquiv T x).property
    have hc := congrArg (fun F : SubgroupFunctor G => F.carrier T)
      (D.termFunctor_bound_eq_bot r hG hp hr)
    rw [hc, bot_carrier, Subgroup.mem_bot] at hx
    have he : R.represents.pointsEquiv T x = 1 := Subtype.ext hx
    exact (R.represents.pointsEquiv T).injective
      (he.trans (R.represents.pointsEquiv T).map_one.symm)
  · rintro rfl
    exact Subgroup.one_mem _

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
