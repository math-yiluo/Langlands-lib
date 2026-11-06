import Langlands.Representation.Plancherel.RationalSourceIwasawaIntegration
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual Iwasawa weighted measure and Bochner integration -/

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

local instance sourceIwasawaBochnerPointTopology : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance sourceIwasawaBochnerPointMeasurable : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance sourceIwasawaBochnerPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceIwasawaBochnerFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceIwasawaBochnerPointTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance sourceIwasawaBochnerPointT2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance sourceIwasawaBochnerPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance sourceIwasawaBochnerPointNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance sourceIwasawaBochnerFieldSecondCountable : SecondCountableTopology F := localField_secondCountableTopology F
local instance sourceIwasawaBochnerPointSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableIwasawaBochner (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "M" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "U" => unipotentPoints χ

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The source multiplication map in the order U, M, K. -/
def sourceIwasawaMap (x : U × (M × K)) : RationalPoint F G.X :=
  (x.1 : RationalPoint F G.X) * x.2.1 * (x.2.2 : RationalPoint F G.X)

theorem continuous_sourceIwasawaMap : Continuous (sourceIwasawaMap χ K) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-- The inverse modulus on the actual source product. -/
def sourceIwasawaDensity (x : U × (M × K)) : ℝ≥0∞ :=
  inverseLeviModulus χ x.2.1

theorem measurable_sourceIwasawaDensity : Measurable (sourceIwasawaDensity χ K) :=
  (measurable_inverseLeviModulus χ).comp (measurable_fst.comp measurable_snd)

theorem sourceIwasawaDensity_lt_top (x : U × (M × K)) :
    sourceIwasawaDensity χ K x < ⊤ :=
  ENNReal.coe_lt_top

/-- The original common-compact product du dm dk, before the density. -/
def sourceIwasawaProductHaar : Measure (U × (M × K)) :=
  (radicalHaar χ K hK).prod
    ((leviHaar χ K hK).prod (compactHaar K hK))

/-- The literal source measure: push forward delta(m)^(-1) du dm dk. -/
def sourceIwasawaMeasure : Measure (RationalPoint F G.X) :=
  ((sourceIwasawaProductHaar χ K hK).withDensity (sourceIwasawaDensity χ K)).map
    (sourceIwasawaMap χ K)

theorem lintegral_sourceIwasawaMeasure (f : RationalPoint F G.X → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g ∂(sourceIwasawaMeasure χ K hK) =
      ∫⁻ u : U, ∫⁻ m : M, inverseLeviModulus χ m *
        ∫⁻ k : K, f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))
          ∂(compactHaar K hK)
          ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  have hmap := (continuous_sourceIwasawaMap χ K).measurable
  have hpair : Measurable (fun x : U × (M × K) =>
      sourceIwasawaDensity χ K x * f (sourceIwasawaMap χ K x)) :=
    (measurable_sourceIwasawaDensity χ K).mul (hf.comp hmap)
  rw [sourceIwasawaMeasure, lintegral_map hf hmap,
    lintegral_withDensity_eq_lintegral_mul _
      (g := fun x => f (sourceIwasawaMap χ K x)) (measurable_sourceIwasawaDensity χ K)
      (hf.comp hmap)]
  change (∫⁻ x, sourceIwasawaDensity χ K x * f (sourceIwasawaMap χ K x)
    ∂(sourceIwasawaProductHaar χ K hK)) = _
  rw [sourceIwasawaProductHaar, lintegral_prod _ hpair.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hsection : Measurable (fun y : M × K =>
      sourceIwasawaDensity χ K (u, y) * f (sourceIwasawaMap χ K (u, y))) :=
    hpair.comp measurable_prodMk_left
  rw [lintegral_prod _ hsection.aemeasurable]
  refine lintegral_congr fun m => ?_
  change (∫⁻ k : K, inverseLeviModulus χ m *
    f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))
      ∂(compactHaar K hK)) = _
  exact lintegral_const_mul _ (f := fun k : K =>
    f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))) (hf.comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val).measurable)

/-- The literal weighted U,M,K pushforward equals the original ambient Haar,
with actual factorization and compact-limit stability explicit. -/
theorem ambientHaar_eq_sourceIwasawaMeasure
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    ambientHaar K hK = sourceIwasawaMeasure χ K hK := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_eq_iwasawa_source_order_of_limit_stable χ K hK hPK hstable f hf,
    lintegral_sourceIwasawaMeasure χ K hK f hf]

section Bochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ambient integrability supplies integrability of the weighted U,M,K
pullback with respect to the original product Haar measures. -/
theorem integrable_sourceIwasawa_pullback
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    Integrable (fun x : U × (M × K) =>
      (sourceIwasawaDensity χ K x).toReal • f (sourceIwasawaMap χ K x))
      (sourceIwasawaProductHaar χ K hK) := by
  have hfm : Integrable f (sourceIwasawaMeasure χ K hK) := by
    rwa [← ambientHaar_eq_sourceIwasawaMeasure χ K hK hPK hstable]
  have hcomp := hfm.comp_measurable (continuous_sourceIwasawaMap χ K).measurable
  exact (integrable_withDensity_iff_integrable_smul'
    (measurable_sourceIwasawaDensity χ K)
    (Filter.Eventually.of_forall (sourceIwasawaDensity_lt_top χ K))).mp hcomp

/-- Bochner integration over the actual inverse-modulus-weighted Iwasawa
product, at the original ambient Haar normalization. -/
theorem integral_eq_iwasawa_source_product_of_limit_stable
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    ∫ g, f g ∂(ambientHaar K hK) =
      ∫ x : U × (M × K),
        (sourceIwasawaDensity χ K x).toReal • f (sourceIwasawaMap χ K x)
          ∂(sourceIwasawaProductHaar χ K hK) := by
  have hfm : Integrable f (sourceIwasawaMeasure χ K hK) := by
    rwa [← ambientHaar_eq_sourceIwasawaMeasure χ K hK hPK hstable]
  rw [ambientHaar_eq_sourceIwasawaMeasure χ K hK hPK hstable,
    sourceIwasawaMeasure,
    integral_map (continuous_sourceIwasawaMap χ K).measurable.aemeasurable
      hfm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_sourceIwasawaDensity χ K)
      (Filter.Eventually.of_forall (sourceIwasawaDensity_lt_top χ K))]

/-- Waldspurger's first integration formula in U,M,K order for every
ambient Bochner-integrable function. -/
theorem integral_eq_iwasawa_source_order_of_limit_stable
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    {f : RationalPoint F G.X → E} (hf : Integrable f (ambientHaar K hK)) :
    ∫ g, f g ∂(ambientHaar K hK) =
      ∫ u : U, ∫ m : M, (inverseLeviModulus χ m).toReal •
        ∫ k : K, f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))
          ∂(compactHaar K hK) ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  rw [integral_eq_iwasawa_source_product_of_limit_stable χ K hK hPK hstable hf]
  have hprod := integrable_sourceIwasawa_pullback χ K hK hPK hstable hf
  rw [sourceIwasawaProductHaar] at hprod ⊢
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [hprod.prod_right_ae] with u hu
  rw [integral_prod _ hu]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun m => ?_
  change (∫ k : K, (inverseLeviModulus χ m).toReal •
    f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))
      ∂(compactHaar K hK)) = _
  exact integral_smul _ _

end Bochner

end Langlands.Plancherel.RationalDynamicSource
