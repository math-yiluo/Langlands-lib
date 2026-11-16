import Langlands.GroupScheme.Reductive.AffinePinnedAtlasSolutionGeometry
import Langlands.GroupScheme.Reductive.BasedAffineCentralizer
import Langlands.GroupScheme.Torus.Locality
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.RelativeDescent
import Langlands.GroupScheme.Descent.RelativeSolvedData

/-! # Maximal tori in actual solutions of a corrected pinned atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

/-- An actual centralizer presentation is invariant under an ambient isomorphism. -/
theorem range_eq_centralizer_comp_iso_iff {S : Scheme.{u}}
    {H G G' : GroupScheme S} (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ G) (e : G ≅ G') :
    SubgroupFunctor.range (i ≫ e.hom) = centralizer (χ ≫ e.hom) ↔
      SubgroupFunctor.range i = centralizer χ := by
  constructor
  · intro h
    rw [centralizer_eq_comap_of_iso χ e, ← h]
    ext T x
    simp only [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap,
      Grp.comp_hom_hom, ← Category.assoc]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ e.hom.hom.hom) hy⟩,
      fun ⟨y, hy⟩ => ⟨y, (cancel_mono e.hom.hom.hom).mp hy⟩⟩
  · intro h
    have h' : SubgroupFunctor.range ((i ≫ e.hom) ≫ e.inv) =
        centralizer ((χ ≫ e.hom) ≫ e.inv) := by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
    rw [centralizer_eq_comap_of_iso (χ ≫ e.hom) e.symm]
    change SubgroupFunctor.range (i ≫ e.hom) =
      (centralizer ((χ ≫ e.hom) ≫ e.inv)).comap e.inv
    rw [← h']
    ext T x
    simp only [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap,
      Grp.comp_hom_hom, ← Category.assoc]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ e.inv.hom.hom) hy⟩,
      fun ⟨y, hy⟩ => ⟨y, (cancel_mono e.inv.hom.hom).mp hy⟩⟩

end Dynamic

/-- A closed torus inclusion is fibrewise maximal if it is so on every member
of an étale covering family. -/
theorem IsFibrewiseMaximalTorus.of_etaleCover {S : Scheme.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S} {t : T.toGrp ⟶ G}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (ht : IsClosedSubgroup t)
    (h : ∀ j, IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange (𝒰.f j)).obj T)
      ((GroupScheme.baseChange (𝒰.f j)).map t)) : IsFibrewiseMaximalTorus t := by
  intro s
  obtain ⟨j, x, hx⟩ := 𝒰.exists_eq s
  let b := (𝒰.X j).fromSpecResidueField x
  have hm := isMaximalTorus_of_baseChange_comp (𝒰.f j) b T t (h j x)
  have hr := isMaximalTorus_residueFibre_of_fieldPoint ht (b ≫ 𝒰.f j) hm
  have hpoint : (b ≫ 𝒰.f j) (IsLocalRing.closedPoint ((𝒰.X j).residueField x)) = s := by
    change 𝒰.f j ((𝒰.X j).fromSpecResidueField x _) = s
    rw [Scheme.fromSpecResidueField_apply, hx]
  exact hpoint ▸ hr

namespace AffinePinnedAtlas

open Descent Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (s : Solution (A.datum P))
    {Z : GroupScheme S} (z : Z ⟶ s.obj)
    (hz : (centralizer (A.descendedCocharacter P s)).IsRepresentedBy z)

/-- The actual centralizer on a chart is its prescribed coordinate split torus. -/
def centralizerChartIso (i : S) :
    (baseChange (A.chart i).map).obj Z ≅
      splitTorus (A.chart i).model.base (A.chart i).model.coordinates := by
  let C := A.chart i
  let M := C.model
  let e := A.solutionChartIso P s i
  have hrep : (centralizer (BasedBorelTransport.cocharacter M.inclusion
      M.rootDatum M.basis)).IsRepresentedBy ((baseChange C.map).map z ≫ e.hom) := by
    have h := hz.baseChange C.map
    rw [← centralizer_baseChange] at h
    have heq := (range_eq_centralizer_comp_iso_iff _ _ e).mpr h.2
    rw [A.descendedCocharacter_on_chart P s i] at heq
    exact ⟨(h.comp_iso e).1, heq⟩
  exact AffineRegularBorel.centralizerIso_positiveCorootSum M.inclusion
    M.rootDatum M.basis M.fibrewiseRootDatum M.reductive M.closed M.maximal _ hrep

/-- The centralizer chart comparison respects both actual inclusions. -/
theorem centralizerChartIso_hom_comp (i : S) :
    (A.centralizerChartIso P s z hz i).hom ≫ (A.chart i).model.inclusion =
      (baseChange (A.chart i).map).map z ≫ (A.solutionChartIso P s i).hom := by
  dsimp only [centralizerChartIso, AffineRegularBorel.centralizerIso_positiveCorootSum]
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

include z hz in
/-- Every actual representative of the descended centralizer is a relative torus. -/
theorem isTorus_descendedCocharacter : RelativeTorus.IsTorus Z := by
  apply RelativeTorus.IsTorus.of_etaleCover A.cover
  change ∀ i : S, RelativeTorus.IsTorus ((baseChange (A.chart i).map).obj Z)
  intro i
  exact RelativeTorus.IsTorus.of_isSplitTorus
    (IsSplitTorus.of_iso (A.centralizerChartIso P s z hz i) (isSplitTorus_splitTorus _))

omit z hz in
/-- A closed commutative representative of the descended centralizer is maximal
on every residue-field fibre. -/
theorem isFibrewiseMaximalTorus_descendedCocharacter
    {T : CommGroupScheme S} (t : T.toGrp ⟶ s.obj)
    (ht : IsClosedSubgroup t)
    (hrep : (centralizer (A.descendedCocharacter P s)).IsRepresentedBy t) :
    IsFibrewiseMaximalTorus t := by
  apply IsFibrewiseMaximalTorus.of_etaleCover A.cover ht
  change ∀ i : S, IsFibrewiseMaximalTorus
    (T := (CommGroupScheme.baseChange (A.chart i).map).obj T)
      ((baseChange (A.chart i).map).map t)
  intro i
  have hm := (A.chart i).model.maximal.iso_comp
    (T' := (CommGroupScheme.baseChange (A.chart i).map).obj T)
    (A.centralizerChartIso P s t hrep i)
  rw [A.centralizerChartIso_hom_comp P s t hrep i] at hm
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    hm.comp_iso (A.solutionChartIso P s i).symm

end AffinePinnedAtlas

end Langlands.GroupScheme
