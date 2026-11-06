import Langlands.Representation.Plancherel.SemidirectSourceHaarNormalization
import Langlands.Representation.Plancherel.SemidirectSourceGammaIntegral
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology
import Langlands.Representation.Aubert.General.RationalLeviRegularity
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant

/-! # The actual rational dynamic measures at the common compact scale -/

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
local instance subgroupSecondCountable (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => (SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀)
local notation "M" => (SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀)
local notation "U" => unipotentPoints χ
local notation "dec" => dynamic_isSemidirectDecomposition χ X₀
local notation "hp" => continuous_dynamic_projection F G χ

omit [LocallyOfFiniteType G.X.hom] in
/-- Closedness of the literal Levi follows from the published continuous
dynamic projection and closed parabolic. -/
theorem isClosed_levi :
    IsClosed (M : Set (RationalPoint F G.X)) :=
  (dec).isClosed_levi_of_continuous_projection (isClosed_dynamic_parabolic F G χ) hp

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The existing normalized Haar on the actual dynamic parabolic. -/
abbrev parabolicHaar : Measure P :=
  subgroupCompactOpenHaar K hK P (isClosed_dynamic_parabolic F G χ)

/-- The existing normalized Haar on the actual dynamic centralizer. -/
abbrev leviHaar : Measure M :=
  subgroupCompactOpenHaar K hK M (isClosed_levi χ)

/-- The existing normalized Haar on the actual dynamic radical. -/
abbrev radicalHaar : Measure U :=
  subgroupCompactOpenHaar K hK U (isClosed_unipotentPoints χ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The required compact splitting is exactly stability under the actual
dynamic limit, with no independently chosen projection. -/
theorem compact_split_iff_limit_stable :
    (∀ (m : M) (u : U),
      (m : RationalPoint F G.X) * u ∈ K ↔
        (m : RationalPoint F G.X) ∈ K ∧ (u : RationalPoint F G.X) ∈ K) ↔
    (∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) := by
  simpa only [dynamic_projection_eq_limitHom, OpenSubgroup.mem_toSubgroup] using
    semidirect_compact_split_iff dec K.toSubgroup

/-- Literal source measures give the original normalized parabolic Haar
when the actual compact intersection is stable under the dynamic limit. -/
theorem productParabolicHaar_eq_of_limit_stable
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    semidirectSourceParabolicMeasure dec hp (leviHaar χ K hK) (radicalHaar χ K hK) =
      parabolicHaar χ K hK := by
  exact semidirectSourceParabolicMeasure_eq_subgroupHaar dec hp
    (isClosed_dynamic_parabolic F G χ) (isClosed_levi χ)
    (isClosed_unipotentPoints χ) K hK
    ((compact_split_iff_limit_stable χ K).mpr hstable)

/-- The published compact-open containment theorem discharges right
invariance of the literal radical measure. -/
instance radicalHaar_rightInvariant : (radicalHaar χ K hK).IsMulRightInvariant := by
  apply compactOpenHaarAlong_isMulRightInvariant_of_cover K hK (U).subtype
    (isClosed_unipotentPoints χ).isClosedEmbedding_subtypeVal
  intro u
  obtain ⟨C, hC, hu⟩ := exists_compactOpenSubgroup χ {u} isCompact_singleton
  exact ⟨C, hC, hu (Set.mem_singleton u)⟩

/-- Inversion preserves the same actual radical measure and its scale. -/
instance radicalHaar_invInvariant : (radicalHaar χ K hK).IsInvInvariant := by
  let sourceMu := radicalHaar χ K hK
  have : sourceMu.inv.Regular := Measure.Regular.map (Homeomorph.inv U)
  refine ⟨?_⟩
  apply compactOpenHaarAlong_eq_of_mass_one K hK (U).subtype
    (isClosed_unipotentPoints χ).isClosedEmbedding_subtypeVal sourceMu.inv
  rw [Measure.inv_apply]
  have hset : ({u : U | (u : RationalPoint F G.X) ∈ K} : Set U)⁻¹ =
      {u : U | (u : RationalPoint F G.X) ∈ K} := by
    ext u
    exact K.inv_mem_iff
  change sourceMu ({u : U | (u : RationalPoint F G.X) ∈ K} : Set U)⁻¹ = 1
  rw [hset]
  exact subgroupCompactOpenHaar_mass K hK U (isClosed_unipotentPoints χ)

/-- The opposite cocharacter used in the actual rational open cell. -/
abbrev oppositeCocharacter :
    (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G :=
  CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ

local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The actual source gamma uses original-subgroup Haar measures fixed
before any Iwasawa component or analytic identity. -/
def gamma : ℝ≥0∞ :=
  openCellConstant (parabolicHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK) K

/-- Canonical semidirect coordinates give this same rational source gamma. -/
theorem gamma_eq_semidirect_of_limit_stable
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    gamma χ K hK =
      semidirectSourceGamma dec hp (leviHaar χ K hK) (radicalHaar χ K hK)
        (radicalHaar (oppositeCocharacter χ) K hK) K := by
  unfold gamma semidirectSourceGamma
  rw [productParabolicHaar_eq_of_limit_stable χ K hK hstable]

section Iwasawa

/-- The actual scalar used by the source gamma integral. -/
def iwasawaModulus
    (hFactor : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (g : RationalPoint F G.X) : ℝ :=
  sourceIwasawaModulus dec hp (isClosed_unipotentPoints χ) K hFactor g

include hK in
/-- The actual scalar modulus is locally constant without choosing
continuous parabolic or Levi components. -/
theorem isLocallyConstant_iwasawaModulus
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X)) :
    IsLocallyConstant (iwasawaModulus χ K hPK) :=
  isLocallyConstant_sourceIwasawaModulus dec hp (isClosed_unipotentPoints χ)
    K hPK (isClosed_dynamic_parabolic F G χ) hK

/-- At the exact common-compact scale the literal source lower integral
requires only the displayed limit stability and Levi right invariance.
Neither reductive unimodularity nor convergence is asserted here. -/
theorem gamma_eq_lintegral_of_levi_rightInvariant
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    [(leviHaar χ K hK).IsMulRightInvariant]
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    gamma χ K hK =
      ∫⁻ v : V, ENNReal.ofReal (iwasawaModulus χ K hPK v)
        ∂(radicalHaar (oppositeCocharacter χ) K hK) := by
  rw [gamma_eq_semidirect_of_limit_stable χ K hK hstable]
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  exact semidirectSourceGamma_eq_lintegral_ofReal dec hp
    (isClosed_unipotentPoints χ) K hPK (leviHaar χ K hK) (radicalHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK)
    ((compact_split_iff_limit_stable χ K).mpr hstable)
    (subgroupCompactOpenHaar_mass K hK M (isClosed_levi χ))
    (subgroupCompactOpenHaar_mass K hK U (isClosed_unipotentPoints χ))

end Iwasawa

end Langlands.Plancherel.RationalDynamicSource
