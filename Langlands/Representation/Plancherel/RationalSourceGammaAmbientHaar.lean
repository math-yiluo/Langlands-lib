import Langlands.Representation.Plancherel.RationalSourceGammaIntegral
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RestrictedOpenCellGamma
import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Representation.RankinSelberg.Measures

/-! # Actual rational gamma from the common-compact ambient Haar -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
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
  rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableAmbient (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The existing regular ambient Haar, with the same compact of mass one.
It is independent of any cocharacter. -/
abbrev ambientHaar : Measure (RationalPoint F G.X) :=
  RankinSelberg.normalizedCompactOpenHaar K hK

@[simp] theorem ambientHaar_self :
    ambientHaar K hK (K : Set (RationalPoint F G.X)) = 1 :=
  RankinSelberg.normalizedCompactOpenHaar_self K hK

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => (SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀)
local notation "V" => unipotentPoints (oppositeCocharacter χ)
local notation "dec" => dynamic_isSemidirectDecomposition χ X₀
local notation "hp" => continuous_dynamic_projection F G χ

/-- Radical elements preserve every ambient left Haar under right translation,
by compact-open containment and regularity in the canonical point topology. -/
theorem map_mul_right_eq_self_of_unipotent
    (mu : Measure (RationalPoint F G.X)) [mu.IsHaarMeasure]
    (v : unipotentPoints χ) :
    Measure.map (fun g : RationalPoint F G.X => g * (v : RationalPoint F G.X)) mu =
      mu := by
  obtain ⟨C, hC, hv⟩ := exists_compactOpenSubgroup χ {v} isCompact_singleton
  let D : Subgroup (RationalPoint F G.X) :=
    C.toSubgroup.map (unipotentPoints χ).subtype
  have hD : IsCompact (D : Set (RationalPoint F G.X)) := by
    change IsCompact ((unipotentPoints χ).subtype '' (C : Set (unipotentPoints χ)))
    exact hC.image continuous_subtype_val
  have hvD : (v : RationalPoint F G.X) ∈ D :=
    ⟨v, hv (Set.mem_singleton v), rfl⟩
  exact CompactFactorization.map_mul_right_eq_self_of_mem mu D hD hvD

/-- The common-compact ambient Haar has the required right invariance along
the actual radical, without a whole-group right-invariance instance. -/
theorem map_mul_right_ambientHaar_of_unipotent (v : unipotentPoints χ) :
    Measure.map (fun g : RationalPoint F G.X => g * (v : RationalPoint F G.X))
      (ambientHaar K hK) = ambientHaar K hK :=
  map_mul_right_eq_self_of_unipotent χ (ambientHaar K hK) v

section Smooth

variable [Smooth G.X.hom]

/-- Smoothness supplies the actual open embedding; radical translations and
the common-compact ambient Haar give finite positive gamma. -/
theorem gamma_ne_zero_ne_top_of_smooth :
    gamma χ K hK ≠ 0 ∧ gamma χ K hK ≠ ⊤ := by
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  exact openCellConstant_ne_zero_ne_top_of_rightInvariantOn (ambientHaar K hK)
    (parabolicHaar χ K hK) (radicalHaar (oppositeCocharacter χ) K hK)
    (map_mul_right_ambientHaar_of_unipotent K hK (oppositeCocharacter χ))
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) K hK

theorem gammaReal_pos_of_smooth : 0 < gammaReal χ K hK := by
  obtain ⟨hzero, htop⟩ := gamma_ne_zero_ne_top_of_smooth K hK χ
  exact ENNReal.toReal_pos hzero htop

/-- The original gamma is recovered exactly from its real value. -/
theorem ofReal_gammaReal_of_smooth :
    ENNReal.ofReal (gammaReal χ K hK) = gamma χ K hK :=
  ENNReal.ofReal_toReal (gamma_ne_zero_ne_top_of_smooth K hK χ).2

/-- Actual source-modulus convergence needs only the displayed Iwasawa,
compact-limit stability and Levi right-invariance premises. -/
theorem integrable_iwasawaModulus_of_levi_rightInvariant
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    [(leviHaar χ K hK).IsMulRightInvariant]
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    Integrable (fun v : V => iwasawaModulus χ K hPK v)
      (radicalHaar (oppositeCocharacter χ) K hK) := by
  refine ⟨((isLocallyConstant_iwasawaModulus χ K hK hPK).continuous.comp
    continuous_subtype_val).aestronglyMeasurable, ?_⟩
  have hnonneg : ∀ v : V, 0 ≤ iwasawaModulus χ K hPK v := fun v =>
    (sourceIwasawaModulus_pos dec hp (isClosed_unipotentPoints χ) K hPK v).le
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg),
    ← gamma_eq_lintegral_of_levi_rightInvariant χ K hK hPK hstable]
  exact lt_top_iff_ne_top.mpr (gamma_ne_zero_ne_top_of_smooth K hK χ).2

/-- The convergent actual source integral equals the same real gamma, with
no ambient measure or ambient right-invariance hypothesis. -/
theorem gammaReal_eq_integral_of_levi_rightInvariant
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    [(leviHaar χ K hK).IsMulRightInvariant]
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    gammaReal χ K hK =
      ∫ v : V, iwasawaModulus χ K hPK v
        ∂(radicalHaar (oppositeCocharacter χ) K hK) := by
  have hnonneg : ∀ v : V, 0 ≤ iwasawaModulus χ K hPK v := fun v =>
    (sourceIwasawaModulus_pos dec hp (isClosed_unipotentPoints χ) K hPK v).le
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
    (integrable_iwasawaModulus_of_levi_rightInvariant K hK χ hPK hstable).aestronglyMeasurable,
    ← gamma_eq_lintegral_of_levi_rightInvariant χ K hK hPK hstable]
  rfl

end Smooth

end Langlands.Plancherel.RationalDynamicSource
