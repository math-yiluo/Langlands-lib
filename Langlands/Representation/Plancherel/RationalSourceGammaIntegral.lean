import Langlands.Representation.Plancherel.RationalDynamicSourceHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LocalOpenCellGamma
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints

/-! # Convergence of the actual rational source gamma integral -/

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
local instance subgroupSecondCountableIntegral (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => (SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀)
local notation "V" => unipotentPoints (oppositeCocharacter χ)
local notation "dec" => dynamic_isSemidirectDecomposition χ X₀
local notation "hp" => continuous_dynamic_projection F G χ

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The real value of the existing gamma with its unchanged common-compact
normalization, before imposing any Iwasawa factorization. -/
def gammaReal : ℝ :=
  (gamma χ K hK).toReal

section Finiteness

variable [Smooth G.X.hom]
  (mu : Measure (RationalPoint F G.X)) [mu.IsHaarMeasure] [mu.IsMulRightInvariant]

include mu in
/-- The actual open embedding suffices for positivity and finiteness.
Ambient right invariance remains explicit; conullness is not needed. -/
theorem gamma_ne_zero_ne_top :
    gamma χ K hK ≠ 0 ∧ gamma χ K hK ≠ ⊤ := by
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  exact openCellConstant_ne_zero_ne_top_of_isOpenEmbedding mu
    (parabolicHaar χ K hK) (radicalHaar (oppositeCocharacter χ) K hK)
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) K hK

include mu in
theorem gammaReal_pos : 0 < gammaReal χ K hK := by
  obtain ⟨hzero, htop⟩ := gamma_ne_zero_ne_top χ K hK mu
  exact ENNReal.toReal_pos hzero htop

include mu in
/-- Passing to the real value loses no mass and introduces no new scalar. -/
theorem ofReal_gammaReal : ENNReal.ofReal (gammaReal χ K hK) = gamma χ K hK :=
  ENNReal.ofReal_toReal (gamma_ne_zero_ne_top χ K hK mu).2

section Iwasawa

include mu in
/-- The source's actual scalar modulus is Bochner integrable, by its
existing local constancy and the finite local open-cell gamma. -/
theorem integrable_iwasawaModulus
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
  exact lt_top_iff_ne_top.mpr (gamma_ne_zero_ne_top χ K hK mu).2

include mu in
/-- The convergent source integral equals the real value of the original
normalized gamma. No full-cell conullness is used. -/
theorem gammaReal_eq_integral
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
    (integrable_iwasawaModulus χ K hK mu hPK hstable).aestronglyMeasurable,
    ← gamma_eq_lintegral_of_levi_rightInvariant χ K hK hPK hstable]
  rfl

end Iwasawa
end Finiteness

end Langlands.Plancherel.RationalDynamicSource
