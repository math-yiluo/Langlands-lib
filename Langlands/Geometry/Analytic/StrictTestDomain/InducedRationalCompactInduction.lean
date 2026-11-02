import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactSupport
import Langlands.Representation.Induction.OpenAdjunction

/-! # Compact induction of full sections on an actual rational quotient spectrum -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport.CompactSections

open Langlands.CompactAction.LocallyConstantModule
open Langlands.Induction

variable (X : ρ.OpenSubgroupTransport)

/-- The full local-spectrum section representation with the original diagonal action. -/
abbrev localRepresentation (M : SmoothRep.{r, v, w} R G) :=
  diagonalRepresentation (X := X.LocalSpectrum)
    (M.representation.comp X.subgroup.toSubgroup.subtype)

/-- All local sections are smooth; compactness is used without a coefficient topology. -/
theorem localRepresentation_isSmooth (M : SmoothRep.{r, v, w} R G) :
    IsSmooth (localRepresentation X M) :=
  diagonalRepresentation_isSmooth _
    (isSmooth_comp X.subgroup.toSubgroup.subtype continuous_subtype_val M.isSmooth)

/-- Full local sections and pointwise original coefficient intertwiners. -/
def localCoefficientFunctor :
    SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u w} R X.subgroup.toSubgroup where
  obj M := SmoothRep.of (localRepresentation X M) (localRepresentation_isSmooth X M)
  map b := SmoothRep.ofHom (coefficientIntertwiner
    (X := X.LocalSpectrum) (resIntertwining X.subgroup.toSubgroup _ (SmoothRep.hom b)))
  map_id _ := by ext s x; rfl
  map_comp _ _ := by ext s x; rfl

/-- Actual compact induction of the entire local-spectrum coefficient module. -/
def compactInducedCoefficientFunctor :
    SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G :=
  localCoefficientFunctor X ⋙ SmoothRep.toRep ⋙ compactInductionFunctor X.subgroup.toSubgroup

/-- Inversion converts the geometric left-coset labels to induction's right-coset labels. -/
def inverseComponent :
    G ⧸ X.subgroup.toSubgroup → LeftQuotient X.subgroup.toSubgroup :=
  Quotient.lift (fun a : G => quotientMap X.subgroup.toSubgroup a⁻¹) (by
    intro a b hab
    apply (quotientMap_eq_iff X.subgroup.toSubgroup _ _).mpr
    simpa using X.subgroup.inv_mem (QuotientGroup.leftRel_apply.mp hab))

@[simp]
theorem inverseComponent_mk (a : G) :
    inverseComponent X (a : G ⧸ X.subgroup.toSubgroup) =
      quotientMap X.subgroup.toSubgroup a⁻¹ := rfl

/-- Twisted restriction to a chart, retaining all local section values. -/
def inductionCoordinate (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) (g : G) :
    LocallyConstant X.LocalSpectrum M :=
  LocallyConstant.mapₗ R (M.representation g)
    (f.val.comap (X.inducedChart g⁻¹))

@[simp]
theorem inductionCoordinate_apply (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) (g : G) (x : X.LocalSpectrum) :
    inductionCoordinate X M f g x =
      M.representation g (f.val (X.inducedMk g⁻¹ x)) := rfl

theorem inductionCoordinate_covariant (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) (h : X.subgroup.toSubgroup) (g : G) :
    inductionCoordinate X M f ((h : G) * g) =
      localRepresentation X M h (inductionCoordinate X M f g) := by
  apply LocallyConstant.ext
  intro x
  change M.representation ((h : G) * g)
      (f.val (X.inducedMk (((h : G) * g)⁻¹) x)) =
    M.representation (h : G) (M.representation g
      (f.val (X.inducedMk g⁻¹ (h⁻¹ • x))))
  rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 2
  exact congrArg f.val (X.inducedChart_mul_subgroup g⁻¹ h⁻¹ x)

theorem inductionCoordinate_action (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) (a g : G) :
    inductionCoordinate X M ((smoothRepresentation X M).representation a f) g =
      inductionCoordinate X M f (g * a) := by
  apply LocallyConstant.ext
  intro x
  change M.representation g (M.representation a
      (f.val (a⁻¹ • X.inducedMk g⁻¹ x))) =
    M.representation (g * a) (f.val (X.inducedMk ((g * a)⁻¹) x))
  rw [← Module.End.mul_apply, ← map_mul, inducedMk_smul, mul_inv_rev]

theorem finite_quotientSupport_inductionCoordinate
    (M : SmoothRep.{r, v, w} R G) (f : Functions (R := R) (V := M) X) :
    (quotientSupport X.subgroup.toSubgroup (inductionCoordinate X M f)).Finite := by
  classical
  apply ((finite_componentSupport X f).image (inverseComponent X)).subset
  rintro _ ⟨g, hg, rfl⟩
  have hx : ∃ x : X.LocalSpectrum, f.val (X.inducedMk g⁻¹ x) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hg
    apply LocallyConstant.ext
    intro x
    change M.representation g (f.val (X.inducedMk g⁻¹ x)) = 0
    rw [hn x, map_zero]
  obtain ⟨x, hx⟩ := hx
  exact ⟨QuotientGroup.mk (g⁻¹ : G),
    ⟨X.inducedMk g⁻¹ x, hx, rfl⟩, by simp⟩

/-- Construct the compactly induced function, deriving its uniform stabilizer
from the proved smoothness of the entire compact-support representation. -/
def toCompactInduction (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) :
    CompactFunctions X.subgroup.toSubgroup (localRepresentation X M) := by
  let J := Classical.choose ((smoothRepresentation X M).isSmooth f)
  have hJ := Classical.choose_spec ((smoothRepresentation X M).isSmooth f)
  exact compactFunctionOf X.subgroup.toSubgroup (localRepresentation X M)
    (inductionCoordinate X M f) (inductionCoordinate_covariant X M f)
    J (fun j g =>
      (inductionCoordinate_action X M f j g).symm.trans
        (congrArg (fun s => inductionCoordinate X M s g) (hJ j)))
    (finite_quotientSupport_inductionCoordinate X M f).isCompact

@[simp]
theorem toCompactInduction_eval (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) (g : G) (x : X.LocalSpectrum) :
    eval X.subgroup.toSubgroup (localRepresentation X M)
        (toCompactInduction X M f).val g x =
      M.representation g (f.val (X.inducedMk g⁻¹ x)) := by
  unfold toCompactInduction
  rfl

/-- The geometric coordinate map is linear and intertwines the original full-group action. -/
def toCompactInductionIntertwiner (M : SmoothRep.{r, v, w} R G) :
    (smoothRepresentation X M).representation.IntertwiningMap
      (compactInduced X.subgroup.toSubgroup (localRepresentation X M)) where
  toFun := toCompactInduction X M
  map_add' f s := by
    apply compactFunctions_ext
    intro g
    apply LocallyConstant.ext
    intro x
    change M.representation g (f.val (X.inducedMk g⁻¹ x) +
        s.val (X.inducedMk g⁻¹ x)) =
      M.representation g (f.val (X.inducedMk g⁻¹ x)) +
        M.representation g (s.val (X.inducedMk g⁻¹ x))
    exact map_add (M.representation g) _ _
  map_smul' c f := by
    apply compactFunctions_ext
    intro g
    apply LocallyConstant.ext
    intro x
    change M.representation g (c • f.val (X.inducedMk g⁻¹ x)) =
      c • M.representation g (f.val (X.inducedMk g⁻¹ x))
    exact map_smul (M.representation g) c _
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply compactFunctions_ext
    intro g
    exact inductionCoordinate_action X M f a g

/-- The coordinates determine every value on the actual balanced quotient. -/
theorem toCompactInduction_injective (M : SmoothRep.{r, v, w} R G) :
    Function.Injective (toCompactInduction X M) := by
  intro f s h
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    change f.val (X.inducedMk p.1 p.2) = s.val (X.inducedMk p.1 p.2)
    have hh := congrArg
      (fun F : CompactFunctions X.subgroup.toSubgroup (localRepresentation X M) =>
        M.representation p.1
          (eval X.subgroup.toSubgroup (localRepresentation X M) F.val p.1⁻¹ p.2)) h
    simpa only [toCompactInduction_eval, inv_inv, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply] using hh

theorem localChartExtension_apply_of_not_mem
    {V : Type w} [AddCommGroup V] [Module R V] (a : G)
    (f : LocallyConstant X.LocalSpectrum V) {z : X.InducedSpectrum}
    (hz : z ∉ X.inducedChartDomain a) :
    (localChartExtension (R := R) X a f).val z = 0 :=
  chartExtension_apply_of_not_mem X a _ hz

/-- Zero extension on the unit chart becomes the compact-induction unit function. -/
theorem toCompactInduction_localChartExtension (M : SmoothRep.{r, v, w} R G)
    (f : LocallyConstant X.LocalSpectrum M) :
    toCompactInduction X M (localChartExtension X 1 f) =
      unitFunction X.subgroup.toSubgroup X.subgroup.isOpen'
        (localRepresentation X M) (localRepresentation_isSmooth X M) f := by
  classical
  apply compactFunctions_ext
  intro g
  apply LocallyConstant.ext
  intro x
  rw [toCompactInduction_eval, eval_unitFunction]
  by_cases hg : g ∈ X.subgroup.toSubgroup
  · simp only [hg, ↓reduceDIte]
    change M.representation g
        ((localChartExtension X 1 f).val (X.inducedChart g⁻¹ x)) =
      M.representation g (f ((⟨g, hg⟩ : X.subgroup.toSubgroup)⁻¹ • x))
    have hc : X.inducedChart g⁻¹ x =
        X.inducedChart 1 ((⟨g, hg⟩ : X.subgroup.toSubgroup)⁻¹ • x) := by
      simpa only [one_mul, InvMemClass.coe_inv] using X.inducedChart_mul_subgroup 1
        ((⟨g, hg⟩ : X.subgroup.toSubgroup)⁻¹) x
    rw [hc, localChartExtension_apply]
  · simp only [hg, ↓reduceDIte]
    have hz : X.inducedMk g⁻¹ x ∉ X.inducedChartDomain 1 := by
      intro hz
      have he := (X.mem_inducedChartDomain_iff 1 _).mp hz
      have hm := QuotientGroup.eq.mp he
      exact hg (by simpa only [inv_inv, mul_one] using hm)
    rw [localChartExtension_apply_of_not_mem X 1 f hz, map_zero]
    rfl

/-- Zero extension on the unit chart intertwines the actual subgroup actions. -/
def unitExtension (M : SmoothRep.{r, v, w} R G) :
    (localRepresentation X M).IntertwiningMap
      ((smoothRepresentation X M).representation.comp X.subgroup.toSubgroup.subtype) where
  toLinearMap := localChartExtension X 1
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    apply toCompactInduction_injective X M
    change toCompactInduction X M (localChartExtension X 1 (localRepresentation X M h f)) =
      toCompactInduction X M
        ((smoothRepresentation X M).representation (h : G) (localChartExtension X 1 f))
    rw [toCompactInduction_localChartExtension]
    have ht := (toCompactInductionIntertwiner X M).isIntertwining
      _ _ (h : G) (localChartExtension X 1 f)
    change toCompactInduction X M
        ((smoothRepresentation X M).representation (h : G) (localChartExtension X 1 f)) =
      compactInduced X.subgroup.toSubgroup (localRepresentation X M) (h : G)
        (toCompactInduction X M (localChartExtension X 1 f)) at ht
    rw [ht, toCompactInduction_localChartExtension]
    exact (unitMap X.subgroup.toSubgroup X.subgroup.isOpen'
      (localRepresentation X M) (localRepresentation_isSmooth X M)).isIntertwining _ _ h f

/-- The inverse is the existing finite coset sum of translates of unit-chart extensions. -/
def fromCompactInductionIntertwiner (M : SmoothRep.{r, v, w} R G) :
    (compactInduced X.subgroup.toSubgroup (localRepresentation X M)).IntertwiningMap
      (smoothRepresentation X M).representation :=
  cosetSum X.subgroup.toSubgroup X.subgroup.isOpen'
    (smoothRepresentation X M).representation (localRepresentation X M) (unitExtension X M)

theorem toCompactInduction_unitExtension (M : SmoothRep.{r, v, w} R G) :
    (resIntertwining X.subgroup.toSubgroup
      (compactInduced X.subgroup.toSubgroup (localRepresentation X M))
      (toCompactInductionIntertwiner X M)).comp (unitExtension X M) =
    unitMap X.subgroup.toSubgroup X.subgroup.isOpen'
      (localRepresentation X M) (localRepresentation_isSmooth X M) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  exact toCompactInduction_localChartExtension X M f

@[simp]
theorem to_fromCompactInduction (M : SmoothRep.{r, v, w} R G)
    (F : CompactFunctions X.subgroup.toSubgroup (localRepresentation X M)) :
    toCompactInduction X M (fromCompactInductionIntertwiner X M F) = F := by
  change (toCompactInductionIntertwiner X M)
    (cosetSum X.subgroup.toSubgroup X.subgroup.isOpen'
      (smoothRepresentation X M).representation (localRepresentation X M)
      (unitExtension X M) F) = F
  rw [← cosetSum_resIntertwining_comp, toCompactInduction_unitExtension]
  exact cosetSum_unitMap X.subgroup.toSubgroup X.subgroup.isOpen'
    (localRepresentation X M) (localRepresentation_isSmooth X M) F

@[simp]
theorem from_toCompactInduction (M : SmoothRep.{r, v, w} R G)
    (f : Functions (R := R) (V := M) X) :
    fromCompactInductionIntertwiner X M (toCompactInduction X M f) = f := by
  apply toCompactInduction_injective X M
  exact to_fromCompactInduction X M _

/-- The inverse has the expected representative-independent pointwise formula. -/
@[simp]
theorem fromCompactInduction_eval (M : SmoothRep.{r, v, w} R G)
    (F : CompactFunctions X.subgroup.toSubgroup (localRepresentation X M))
    (a : G) (x : X.LocalSpectrum) :
    (fromCompactInductionIntertwiner X M F).val (X.inducedMk a x) =
      M.representation a (eval X.subgroup.toSubgroup (localRepresentation X M) F.val a⁻¹ x) := by
  have h := congrArg
    (fun F' : CompactFunctions X.subgroup.toSubgroup (localRepresentation X M) =>
      M.representation a
        (eval X.subgroup.toSubgroup (localRepresentation X M) F'.val a⁻¹ x))
    (to_fromCompactInduction X M F)
  simpa only [toCompactInduction_eval, inv_inv, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply] using h

/-- Full compact sections on the induced rational spectrum are actual compact induction. -/
def compactInductionIso (M : SmoothRep.{r, v, w} R G) :
    (coefficientFunctor X).obj M ≅ (compactInducedCoefficientFunctor X).obj M where
  hom := SmoothRep.ofHom (toCompactInductionIntertwiner X M)
  inv := SmoothRep.ofHom (fromCompactInductionIntertwiner X M)
  hom_inv_id := by
    ext f
    exact from_toCompactInduction X M f
  inv_hom_id := by
    ext F
    exact to_fromCompactInduction X M F

/-- The compact-induction identification retains every original coefficient intertwiner. -/
def compactInductionNatIso :
    (coefficientFunctor X :
      SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G) ≅
        compactInducedCoefficientFunctor X :=
  NatIso.ofComponents (compactInductionIso X) (by
    intro M N b
    ext f
    apply compactFunctions_ext
    intro g
    apply LocallyConstant.ext
    intro x
    change N.representation g (SmoothRep.hom b (f.val (X.inducedMk g⁻¹ x))) =
      SmoothRep.hom b (M.representation g (f.val (X.inducedMk g⁻¹ x)))
    exact ((SmoothRep.hom b).isIntertwining _ _ g _).symm)

end OpenSubgroupTransport.CompactSections

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
