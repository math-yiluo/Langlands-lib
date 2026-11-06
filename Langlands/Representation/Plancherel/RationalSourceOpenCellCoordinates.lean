import Langlands.Representation.Plancherel.RationalSourceGammaAmbientHaar
import Langlands.Representation.Plancherel.RationalOpenCellConullProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RestrictedOpenCellIntegration

/-! # Actual global open-cell integration in the source coordinate order -/

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
local instance subgroupSecondCountableSource (H : Subgroup (RationalPoint F G.X)) :
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

/-- The source Levi modulus is the existing actual radical conjugation
character, independent of the compact used to normalize Haar. -/
abbrev leviModulus : M →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter U (isClosed_unipotentPoints χ) M
    (dec).levi_le_normalizer

/-- The inverse-modulus density in the source's unipotent-first order. -/
def inverseLeviModulus (m : M) : ℝ≥0∞ :=
  (((leviModulus χ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)

theorem measurable_inverseLeviModulus : Measurable (inverseLeviModulus χ) := by
  have hc : Continuous (leviModulus χ) :=
    Weil.continuous_of_open_kernel _
      (HaarModulus.isOpen_ker_closedRestrictCharacter U
        (isClosed_unipotentPoints χ) M (dec).levi_le_normalizer)
  unfold inverseLeviModulus
  simpa only [Function.comp_def, Units.val_inv_eq_inv_val] using
    (ENNReal.continuous_coe.comp (Units.continuous_coe_inv.comp hc)).measurable

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- At the fixed compact scale, actual parabolic Haar decomposes into the
canonical Levi and radical measures whenever the compact limit is stable. -/
theorem lintegral_parabolicHaar_of_limit_stable
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (Φ : P → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ p, Φ p ∂(parabolicHaar χ K hK) =
      ∫⁻ m : M, ∫⁻ u : U, Φ ((dec).coordinates hp (m, u))
        ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  rw [← productParabolicHaar_eq_of_limit_stable χ K hK hstable,
    semidirectSourceParabolicMeasure,
    lintegral_map hΦ ((dec).coordinates hp).continuous.measurable]
  exact lintegral_prod _ (hΦ.comp ((dec).coordinates hp).continuous.measurable).aemeasurable

/-- The global formula in canonical Levi-first coordinates, at the original
common-compact scale and with the opposite variable uninverted. -/
theorem lintegral_eq_levi_radical_of_limit_stable
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(ambientHaar K hK) =
      (gamma χ K hK)⁻¹ *
        ∫⁻ m : M, ∫⁻ u : U, ∫⁻ v : V,
          f ((m : RationalPoint F G.X) * u * (v : RationalPoint F G.X))
            ∂(radicalHaar (oppositeCocharacter χ) K hK)
            ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK) := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have hmass : ambientHaar K hK (K.toSubgroup : Set (RationalPoint F G.X)) = 1 :=
    ambientHaar_self K hK
  have hnull := rationalDynamicOpenCellConull F G hG χ (ambientHaar K hK) inferInstance
  have hglobal := lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn
    (ambientHaar K hK) (parabolicHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK)
    (map_mul_right_ambientHaar_of_unipotent K hK (oppositeCocharacter χ))
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) hnull
    K.isOpen.measurableSet
    (by rw [hmass]; exact one_ne_zero)
    (by rw [hmass]; exact ENNReal.one_ne_top)
  have htwo : (∫⁻ g, f g ∂(ambientHaar K hK)) =
      (gamma χ K hK)⁻¹ * ∫⁻ p : P, ∫⁻ v : V,
        f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X)⁻¹)
          ∂(radicalHaar (oppositeCocharacter χ) K hK) ∂(parabolicHaar χ K hK) := by
    simpa only [hmass, one_mul, gamma] using hglobal.2.2 f hf
  have hinv (p : P) :
      (∫⁻ v : V, f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X)⁻¹)
        ∂(radicalHaar (oppositeCocharacter χ) K hK)) =
      ∫⁻ v : V, f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X))
        ∂(radicalHaar (oppositeCocharacter χ) K hK) :=
    lintegral_inv_eq_self (fun v : V =>
      f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X)))
  simp_rw [hinv] at htwo
  rw [htwo]
  congr 1
  have hΦ : Measurable (fun p : P => ∫⁻ v : V,
      f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X))
        ∂(radicalHaar (oppositeCocharacter χ) K hK)) := by
    exact (hf.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable).lintegral_prod_right'
  exact lintegral_parabolicHaar_of_limit_stable χ K hK hstable _ hΦ

/-- Waldspurger's actual U,M,opposite-U nonnegative formula, retaining the
precise compact-limit stability premise needed for the Haar comparison. -/
theorem lintegral_eq_source_order_of_limit_stable
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(ambientHaar K hK) =
      (gamma χ K hK)⁻¹ *
        ∫⁻ u : U, ∫⁻ m : M, inverseLeviModulus χ m *
          ∫⁻ v : V, f ((u : RationalPoint F G.X) * m * (v : RationalPoint F G.X))
            ∂(radicalHaar (oppositeCocharacter χ) K hK)
            ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  rw [lintegral_eq_levi_radical_of_limit_stable χ K hK hG hstable f hf]
  congr 1
  let Φ : RationalPoint F G.X → ℝ≥0∞ := fun g =>
    ∫⁻ v : V, f (g * (v : RationalPoint F G.X))
      ∂(radicalHaar (oppositeCocharacter χ) K hK)
  have hΦ : Measurable Φ :=
    (hf.comp (continuous_fst.mul
      (continuous_subtype_val.comp continuous_snd)).measurable).lintegral_prod_right'
  have hν := isConjModulus_semidirect_closedCharacter dec (radicalHaar χ K hK)
    (isClosed_unipotentPoints χ)
  change (∫⁻ m : M, ∫⁻ u : U, Φ ((m : RationalPoint F G.X) * u)
      ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK)) = _
  rw [lintegral_levi_unipotent_eq (dec).levi_le_normalizer
    (leviHaar χ K hK) (radicalHaar χ K hK) hν Φ]
  change (∫⁻ m : M, inverseLeviModulus χ m *
      ∫⁻ u : U, Φ ((u : RationalPoint F G.X) * m)
        ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK)) =
    ∫⁻ u : U, ∫⁻ m : M, inverseLeviModulus χ m *
      Φ ((u : RationalPoint F G.X) * m) ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK)
  have hpair : Measurable (fun x : M × U => inverseLeviModulus χ x.1 *
      Φ ((x.2 : RationalPoint F G.X) * x.1)) :=
    ((measurable_inverseLeviModulus χ).comp measurable_fst).mul
      (hΦ.comp ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst)).measurable)
  calc
    _ = ∫⁻ m : M, ∫⁻ u : U, inverseLeviModulus χ m *
        Φ ((u : RationalPoint F G.X) * m)
          ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK) := by
      refine lintegral_congr fun m => ?_
      exact (lintegral_const_mul _ (hΦ.comp
        (continuous_subtype_val.mul continuous_const).measurable)).symm
    _ = _ := lintegral_lintegral_swap hpair.aemeasurable

end Langlands.Plancherel.RationalDynamicSource
