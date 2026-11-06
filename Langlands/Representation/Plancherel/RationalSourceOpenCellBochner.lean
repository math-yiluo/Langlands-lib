import Langlands.Representation.Plancherel.RationalSourceOpenCellCoordinates
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The actual weighted source measure and Bochner integration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance : SecondCountableTopology F := localField_secondCountableTopology F
local instance : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableBochner (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "M" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "U" => unipotentPoints χ
local notation "V" => unipotentPoints (oppositeCocharacter χ)
local notation "dec" => dynamic_isSemidirectDecomposition χ X₀
local notation "hp" => continuous_dynamic_projection F G χ

/-- The source multiplication map in the order U, M, opposite U. -/
def sourceOpenCellMap (x : U × (M × V)) : RationalPoint F G.X :=
  (x.1 : RationalPoint F G.X) * x.2.1 * (x.2.2 : RationalPoint F G.X)

theorem continuous_sourceOpenCellMap : Continuous (sourceOpenCellMap χ) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-- The inverse modulus on the actual source product. -/
def sourceOpenCellDensity (x : U × (M × V)) : ℝ≥0∞ :=
  inverseLeviModulus χ x.2.1

theorem measurable_sourceOpenCellDensity : Measurable (sourceOpenCellDensity χ) :=
  (measurable_inverseLeviModulus χ).comp (measurable_fst.comp measurable_snd)

theorem sourceOpenCellDensity_lt_top (x : U × (M × V)) :
    sourceOpenCellDensity χ x < ⊤ :=
  ENNReal.coe_lt_top

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The original common-compact product du dm dv, before the density. -/
def sourceProductHaar : Measure (U × (M × V)) :=
  (radicalHaar χ K hK).prod
    ((leviHaar χ K hK).prod (radicalHaar (oppositeCocharacter χ) K hK))

/-- The literal source measure: push forward delta(m)^(-1) du dm dv. -/
def sourceOpenCellMeasure : Measure (RationalPoint F G.X) :=
  ((sourceProductHaar χ K hK).withDensity (sourceOpenCellDensity χ)).map
    (sourceOpenCellMap χ)

theorem lintegral_sourceOpenCellMeasure (f : RationalPoint F G.X → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g ∂(sourceOpenCellMeasure χ K hK) =
      ∫⁻ u : U, ∫⁻ m : M, inverseLeviModulus χ m *
        ∫⁻ v : V, f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))
          ∂(radicalHaar (oppositeCocharacter χ) K hK)
          ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have hmap := (continuous_sourceOpenCellMap χ).measurable
  have hpair : Measurable (fun x : U × (M × V) =>
      sourceOpenCellDensity χ x * f (sourceOpenCellMap χ x)) :=
    (measurable_sourceOpenCellDensity χ).mul (hf.comp hmap)
  rw [sourceOpenCellMeasure, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _
      (g := fun x => f (sourceOpenCellMap χ x)) (measurable_sourceOpenCellDensity χ)
      (hf.comp hmap)]
  change (∫⁻ x, sourceOpenCellDensity χ x * f (sourceOpenCellMap χ x)
    ∂(sourceProductHaar χ K hK)) = _
  rw [sourceProductHaar, lintegral_prod _ hpair.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hsection : Measurable (fun y : M × V =>
      sourceOpenCellDensity χ (u, y) * f (sourceOpenCellMap χ (u, y))) :=
    hpair.comp measurable_prodMk_left
  rw [lintegral_prod _ hsection.aemeasurable]
  refine lintegral_congr fun m => ?_
  change (∫⁻ v : V, inverseLeviModulus χ m *
    f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))
      ∂(radicalHaar (oppositeCocharacter χ) K hK)) = _
  exact lintegral_const_mul _ (f := fun v : V =>
    f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))) (hf.comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val).measurable)

/-- The original normalized ambient Haar is gamma inverse times the literal
weighted source pushforward, with compact-limit stability explicit. -/
theorem ambientHaar_eq_inv_gamma_smul_sourceOpenCellMeasure
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    ambientHaar K hK = (gamma χ K hK)⁻¹ • sourceOpenCellMeasure χ K hK := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_eq_source_order_of_limit_stable χ K hK hG hstable f hf,
    lintegral_sourceOpenCellMeasure χ K hK f hf]

section Bochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every ambient-integrable function has an integrable weighted source
pullback; neither separate measurability nor pointwise fiber integrability
is postulated. -/
theorem integrable_sourceOpenCell_pullback
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    Integrable (fun x : U × (M × V) =>
      (sourceOpenCellDensity χ x).toReal • f (sourceOpenCellMap χ x))
      (sourceProductHaar χ K hK) := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨hγ0, hγtop⟩ := gamma_ne_zero_ne_top_of_smooth K hK χ
  have hfm : Integrable f (sourceOpenCellMeasure χ K hK) := by
    apply (integrable_inv_smul_measure hγ0 hγtop).mp
    rwa [← ambientHaar_eq_inv_gamma_smul_sourceOpenCellMeasure χ K hK hG hstable]
  have hcomp := hfm.comp_measurable (continuous_sourceOpenCellMap χ).measurable
  exact (integrable_withDensity_iff_integrable_smul'
    (measurable_sourceOpenCellDensity χ)
    (Filter.Eventually.of_forall (sourceOpenCellDensity_lt_top χ))).mp hcomp

/-- Bochner integration in the actual weighted product coordinates. -/
theorem integral_eq_source_product_of_limit_stable
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    ∫ g, f g ∂(ambientHaar K hK) =
      (gamma χ K hK)⁻¹.toReal • ∫ x : U × (M × V),
        (sourceOpenCellDensity χ x).toReal • f (sourceOpenCellMap χ x)
          ∂(sourceProductHaar χ K hK) := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨hγ0, hγtop⟩ := gamma_ne_zero_ne_top_of_smooth K hK χ
  have hfm : Integrable f (sourceOpenCellMeasure χ K hK) := by
    apply (integrable_inv_smul_measure hγ0 hγtop).mp
    rwa [← ambientHaar_eq_inv_gamma_smul_sourceOpenCellMeasure χ K hK hG hstable]
  rw [ambientHaar_eq_inv_gamma_smul_sourceOpenCellMeasure χ K hK hG hstable,
    integral_smul_measure, sourceOpenCellMeasure,
    integral_map (continuous_sourceOpenCellMap χ).measurable.aemeasurable
      hfm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_sourceOpenCellDensity χ)
      (Filter.Eventually.of_forall (sourceOpenCellDensity_lt_top χ))]

/-- The iterated Bochner formula in Waldspurger's U,M,opposite-U order.
All required product integrability follows from ambient integrability. -/
theorem integral_eq_source_order_of_limit_stable
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    ∫ g, f g ∂(ambientHaar K hK) =
      (gamma χ K hK)⁻¹.toReal •
        ∫ u : U, ∫ m : M, (inverseLeviModulus χ m).toReal •
          ∫ v : V, f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))
            ∂(radicalHaar (oppositeCocharacter χ) K hK)
            ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  rw [integral_eq_source_product_of_limit_stable χ K hK hG hstable hf]
  congr 1
  have hprod := integrable_sourceOpenCell_pullback χ K hK hG hstable hf
  rw [sourceProductHaar] at hprod ⊢
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [hprod.prod_right_ae] with u hu
  rw [integral_prod _ hu]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun m => ?_
  change (∫ v : V, (inverseLeviModulus χ m).toReal •
    f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))
      ∂(radicalHaar (oppositeCocharacter χ) K hK)) = _
  exact integral_smul _ _

end Bochner

end Langlands.Plancherel.RationalDynamicSource
