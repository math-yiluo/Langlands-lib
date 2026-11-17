import Langlands.GroupScheme.Reductive.LocalRankOneNormalizationDescent
import Langlands.GroupScheme.FppfHomLocality
import Mathlib.RingTheory.Ideal.Nonunits

/-! # Rank-one normalization from pointwise etale Weyl data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- An element is a unit if it has a unit image on an affine
neighborhood through every prime of the original ring. -/
theorem isUnit_of_pointwise_affine_image
    {R : Type u} [CommRing R] (c : R)
    (h : ∀ s : Spec (CommRingCat.of R),
      ∃ (A : CommRingCat.{u}) (f : R →+* A) (t : Spec A),
        (Spec.map (CommRingCat.ofHom f)) t = s ∧ IsUnit (f c)) :
    IsUnit c := by
  by_contra hc
  obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
  let s : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  obtain ⟨A, f, t, ht, hu⟩ := h s
  have hmem : f c ∈ t.asIdeal := by
    change c ∈ ((Spec.map (CommRingCat.ofHom f)) t).asIdeal
    rw [ht]
    exact hcm
  exact t.isPrime.ne_top (t.asIdeal.eq_top_of_isUnit_mem hmem hu)

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (a : I → ℤ) (xp xm : Ga R ⟶ G)
    (hp : IsRootParametrization i a xp)
    (hm : IsRootParametrization i (-a) xm)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)

/-- Opposite actual root parametrizations with an open triple cell,
without a locality hypothesis on the base ring. -/
def oppositeCellData : RingRootCell.CellData R where
  G := G
  T := splitTorus.commGroupScheme _ I
  i := i
  xp := xp
  xm := xm
  α := splitTorus.exponentCharacter _ I a
  hxp := hp.equivariant_point
  hxm := by
    have hneg : splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (-a) =
        -splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a :=
      (splitTorus.exponentCharacterLinear _ I).map_neg a
    simpa only [hneg] using hm.equivariant_point
  open_cell := hopen

/-- Actual etale Weyl data through one base point, retaining the
original opposite maps and the prescribed integral torus action. -/
structure EtaleRankOneChart
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (s : Spec (CommRingCat.of R)) where
  ring : CommRingCat.{u}
  algebra : Algebra R ring
  etale : letI := algebra
    Etale (algebraBaseMap R ring)
  covers : letI := algebra
    s ∈ Set.range (algebraBaseMap R ring)
  data : RingRootCell.WeylData ring
  cell_eq : letI := algebra
    data.toCellData = LocalRankOneCell.baseChangeCellData i a xm xp hm hp hopen ring
  normalizes : letI := algebra
    IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec ring) I)
      (splitTorus.baseChangeHom (K := ring) G I i)
      (scalarWeylPoint (LocalSplitRootBaseChange.baseChangeRoot ring xp)
        (LocalSplitRootBaseChange.baseChangeRoot ring xm) (data.betaUnit : ring))
      (splitTorus.exponentCommIso (Spec ring) I e)

variable {i a xp xm hp hm hopen}
    {e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    {s : Spec (CommRingCat.of R)} [hAff : IsAffineHom G.X.hom]

include hAff

/-- The same original dual coefficient has unit inverse-beta image
on every supplied chart. -/
theorem EtaleRankOneChart.normalizationScalar_image
    (E : EtaleRankOneChart i a xp xm hp hm hopen e s)
    {y : Γ((LocalWeylNormalization.dualOver R).left, ⊤)}
    {t : LocalWeylNormalization.dualOver R ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((LocalWeylNormalization.dualOver R).left, ⊤)}
    (hx : rootPoint xp (LocalWeylNormalization.dualOver R) 1 *
        rootPoint xm (LocalWeylNormalization.dualOver R)
          (LocalWeylNormalization.epsSec R) =
      rootPoint xm (LocalWeylNormalization.dualOver R) y *
        ((t ≫ i.hom.hom) * rootPoint xp (LocalWeylNormalization.dualOver R) x)) :
    letI := E.algebra
    algebraMap R E.ring (RingRootCell.DualCell.normalizationScalar x) =
      (↑E.data.betaUnit⁻¹ : E.ring) := by
  let := E.algebra
  let b := algebraBaseMap R E.ring
  have hG : E.data.G = (baseChange b).obj G :=
    congrArg RingRootCell.CellData.G E.cell_eq
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom b))
  let : IsAffine E.data.G.X.left := by
    rw [hG]
    exact isAffine_of_isAffineHom ((baseChange b).obj G).X.hom
  exact LocalRankOneCell.algebraMap_normalizationScalar
    i a xm xp hm hp hopen E.ring E.data E.cell_eq hx

variable (i a xp xm hp hm hopen e)

include hAff in
/-- The original dual coefficient gives one global unit rescaling.
Its prescribed reflection identity is checked on the pointwise etale
charts, without requiring any one chart to cover the whole base. -/
theorem exists_unit_weylNormalization_of_charts
    (charts : ∀ s : Spec (CommRingCat.of R),
      EtaleRankOneChart i a xp xm hp hm hopen e s) :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint xp (scaleHom (d : R) ≫ xm)) e := by
  let D := oppositeCellData i a xp xm hp hm hopen
  obtain ⟨y, t, x, hx⟩ := D.exists_dualFactorization
  let c := RingRootCell.DualCell.normalizationScalar x
  have hc : IsUnit c := by
    apply isUnit_of_pointwise_affine_image c
    intro s
    let E := charts s
    let := E.algebra
    obtain ⟨z, hz⟩ := E.covers
    refine ⟨E.ring, algebraMap R E.ring, z, hz, ?_⟩
    rw [show algebraMap R E.ring c = (↑E.data.betaUnit⁻¹ : E.ring) from
      E.normalizationScalar_image hx]
    exact Units.isUnit _
  let d := hc.unit⁻¹
  have hn : IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i
      (scalarWeylPoint xp xm (d : R))
      (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I e) := by
    apply hom_ext_of_pointwise_etale_baseChange
    intro s
    let E := charts s
    let := E.algebra
    let b := algebraBaseMap R E.ring
    have hmap : Units.map (algebraMap R E.ring).toMonoidHom hc.unit =
        E.data.betaUnit⁻¹ := by
      apply Units.ext
      change algebraMap R E.ring (hc.unit : R) = _
      rw [hc.unit_spec]
      exact E.normalizationScalar_image hx
    have hd : algebraMap R E.ring (d : R) = (E.data.betaUnit : E.ring) := by
      change (Units.map (algebraMap R E.ring).toMonoidHom hc.unit⁻¹ : E.ring) = _
      rw [map_inv, hmap, inv_inv]
    have hnormal : IsNormalizingPoint
        (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
        ((baseChange b).map i)
        (baseChangeBasePoint b G (scalarWeylPoint xp xm (d : R)))
        ((CommGroupScheme.baseChange b).mapIso
          (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I e)) := by
      apply splitTorus.isNormalizingPoint_baseChange_of_coordinates i b e
      rw [baseChangeBasePoint_scalarWeylPoint, hd]
      exact E.normalizes
    refine ⟨Spec E.ring, b, E.etale, E.covers, ?_⟩
    rw [Functor.map_comp, baseChange_innerIso_hom, Functor.map_comp]
    exact hnormal
  exact ⟨d, isWeylPoint_of_isNormalizingPoint hn⟩

/-- A global normalized opposite pair, retaining its actual unit
rescaling and prescribed torus reflection. -/
structure NormalizedOppositePair where
  scalar : Rˣ
  normalizes : IsWeylPoint i (weylPoint xp (scaleHom (scalar : R) ≫ xm)) e

/-- Construct the global normalized pair from the supplied pointwise
etale charts and one original dual-cell factorization. -/
def normalizedOppositePairOfCharts
    (charts : ∀ s : Spec (CommRingCat.of R),
      EtaleRankOneChart i a xp xm hp hm hopen e s) :
    NormalizedOppositePair i xp xm e where
  scalar := (exists_unit_weylNormalization_of_charts i a xp xm hp hm hopen e charts).choose
  normalizes :=
    (exists_unit_weylNormalization_of_charts i a xp xm hp hm hopen e charts).choose_spec

end LocalSplitCell
end Langlands.GroupScheme
