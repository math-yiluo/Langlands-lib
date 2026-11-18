import Langlands.GroupScheme.RelativeLevi.FaceChartOverlapComparison
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching

/-! # Effective descent of the actual canonical face terms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open SubgroupFunctor SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)

local instance termDescentAmbientAffine {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- The actual finite chart family as an etale cover of the original base. -/
def chartCover : S.Cover.{u} (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers (P := @Etale) D.Index
    (fun a : D.Index => Spec (D.charts a.down).2.ring)
    (fun a => (D.charts a.down).2.projection)
    (fun s => by
      obtain ⟨a, y, hy⟩ := D.covers s
      exact ⟨⟨a⟩, y, hy⟩)
    (fun a => (D.charts a.down).2.etale)

/-- The prescribed original term ranges on the actual chart cover. -/
def localTermFunctor (d : ℕ) (a : D.chartCover.I₀) :
    SubgroupFunctor ((baseChange (D.chartCover.f a)).obj G) :=
  range ((D.charts a.down).2.termInclusion d)

/-- Monicity of the original term map follows from the actual represented inclusions. -/
theorem localTermInclusion_mono (d : ℕ) (a : D.chartCover.I₀) :
    Mono ((D.charts a.down).2.termInclusion d).hom.hom := by
  let C := (D.charts a.down).2
  let : Fintype C.coordinateType := C.coordinateFintype
  let : Fintype C.rootType := C.rootFintype
  let : IsAffine ((baseChange C.projection).obj G).X.left :=
    isAffine_of_isAffineHom ((baseChange C.projection).obj G).X.hom
  change Mono ((C.chart.weights.inclusion d).hom.hom ≫
    (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter C.torus C.chart.cocharacter)).hom.hom)
  exact mono_comp' (C.chart.weights.isRepresentedBy_inclusion d).1
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter C.torus C.chart.cocharacter)).1

/-- Every local original term is represented by its actual closed inclusion. -/
theorem localTermFunctor_isClosedRepresentable (d : ℕ) (a : D.chartCover.I₀) :
    (D.localTermFunctor d a).IsClosedRepresentable :=
  ⟨(D.charts a.down).2.termGroup d, (D.charts a.down).2.termInclusion d,
    ⟨D.localTermInclusion_mono d a, rfl⟩,
    (D.charts a.down).2.isClosedSubgroup_termInclusion d⟩

variable (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

include hG hp hr in
/-- Original term ranges agree through the actual pairwise ambient square. -/
theorem localTerm_overlap_range_eq (d : ℕ) (a b : D.chartCover.I₀) :
    range ((baseChange (pullback.fst (D.chartCover.f a) (D.chartCover.f b))).map
        ((D.charts a.down).2.termInclusion d)) =
      range ((baseChange (pullback.snd (D.chartCover.f a) (D.chartCover.f b))).map
        ((D.charts b.down).2.termInclusion d) ≫
          (CoverDescent.overlapSquareIso D.chartCover a b G).inv) := by
  let f := pullback.fst (D.chartCover.f a) (D.chartCover.f b)
  let g := pullback.snd (D.chartCover.f a) (D.chartCover.f b)
  let e := Descent.pullbackComparison (D.chartCover.f a) f
    (g ≫ D.chartCover.f b) pullback.condition G
  apply (SubgroupFunctor.range_comp_iso_eq_iff _ _ e).mp
  have he : (CoverDescent.overlapSquareIso D.chartCover a b G).inv ≫ e.hom =
      (Descent.pullbackComparison (D.chartCover.f b) g (g ≫ D.chartCover.f b) rfl G).hom := by
    simp only [e, f, g, CoverDescent.overlapSquareIso, Descent.squareComparison,
      Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, he]
  exact (D.charts a.down).2.range_restriction_eq (D.charts b.down).2 r hG hp hr
    f g (g ≫ D.chartCover.f b) pullback.condition rfl d

include hG hp hr in
/-- The original chart terms form an actual matching family on all tests. -/
theorem localTermFunctor_isMatching (d : ℕ) :
    CoverDescent.IsMatching D.chartCover (D.localTermFunctor d) :=
  CoverDescent.isMatching_of_overlap_range_eq D.chartCover
    (fun a => (D.charts a.down).2.termGroup d)
    (fun a => (D.charts a.down).2.termInclusion d)
    (D.localTerm_overlap_range_eq r hG hp hr d)

/-- The actual global subgroup condition descended from all original chart terms. -/
def termFunctor (d : ℕ) : SubgroupFunctor G :=
  CoverDescent.subgroup D.chartCover (D.localTermFunctor d)

include hG hp hr in
/-- Restriction of the global all-test condition is exactly the original local term. -/
theorem termFunctor_baseChange (d : ℕ) (a : D.chartCover.I₀) :
    (D.termFunctor d).baseChange (D.chartCover.f a) = D.localTermFunctor d a :=
  CoverDescent.baseChange_subgroup D.chartCover (D.localTermFunctor d)
    (D.localTermFunctor_isMatching r hG hp hr d) a

/-- The actual global closed group representing the canonical term on the original base. -/
def closedTermRepresentative (d : ℕ) : ClosedRepresentative (D.termFunctor d) :=
  CoverDescent.closedRepresentativeEtale D.chartCover (D.localTermFunctor d)
    (D.localTermFunctor_isMatching r hG hp hr d)
    (D.localTermFunctor_isClosedRepresentable d)

/-- Actual restriction of the descended closed term recovers the prescribed chart group. -/
def globalTermChartIso (d : ℕ) (a : D.chartCover.I₀) :
    (baseChange (D.chartCover.f a)).obj (D.closedTermRepresentative r hG hp hr d).group ≅
      (D.charts a.down).2.termGroup d := by
  let R := D.closedTermRepresentative r hG hp hr d
  have hrep := R.represents.baseChange (D.chartCover.f a)
  rw [D.termFunctor_baseChange r hG hp hr d a] at hrep
  exact hrep.isoOfIsRepresentedBy ⟨D.localTermInclusion_mono d a, rfl⟩

/-- The recovery isomorphism preserves the ORIGINAL ambient chart inclusion. -/
theorem globalTermChartIso_hom_comp (d : ℕ) (a : D.chartCover.I₀) :
    (D.globalTermChartIso r hG hp hr d a).hom ≫
        (D.charts a.down).2.termInclusion d =
      (baseChange (D.chartCover.f a)).map
        (D.closedTermRepresentative r hG hp hr d).hom := by
  unfold globalTermChartIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The actual descended term is smooth over the original base. -/
theorem smooth_closedTermRepresentative (d : ℕ) :
    Smooth (D.closedTermRepresentative r hG hp hr d).group.X.hom := by
  apply smooth_of_etaleCover D.chartCover
  intro a
  let e := D.globalTermChartIso r hG hp hr d a
  let : Smooth ((D.charts a.down).2.termGroup d).X.hom :=
    (D.charts a.down).2.smooth_termGroup d
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  rw [← Over.w e.hom.hom.hom]
  infer_instance

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
