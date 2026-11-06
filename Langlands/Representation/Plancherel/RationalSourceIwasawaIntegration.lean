import Langlands.Representation.Plancherel.RationalSourceOpenCellCoordinates
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Actual Iwasawa integration at the common compact normalization -/

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

local instance sourceIwasawaPointTopology : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance sourceIwasawaPointMeasurable : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance sourceIwasawaPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceIwasawaFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceIwasawaPointTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance sourceIwasawaPointT2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance sourceIwasawaPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance sourceIwasawaPointNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance sourceIwasawaFieldSecondCountable : SecondCountableTopology F := localField_secondCountableTopology F
local instance sourceIwasawaPointSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableIwasawa (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "M" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "U" => unipotentPoints χ
local notation "dec" => dynamic_isSemidirectDecomposition χ X₀
local notation "hp" => continuous_dynamic_projection F G χ

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Haar on the supplied compact, using the same compact-intersection
normalization as every other source subgroup. -/
abbrev compactHaar : Measure K :=
  subgroupCompactOpenHaar K hK K.toSubgroup K.isClosed

@[simp] theorem compactHaar_univ :
    compactHaar K hK Set.univ = 1 := by
  have hmass := subgroupCompactOpenHaar_mass K hK K.toSubgroup K.isClosed
  have hset : {k : K.toSubgroup | (k : RationalPoint F G.X) ∈ K} = Set.univ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact k.property
  simpa only [hset] using hmass

instance compactHaar_isProbabilityMeasure :
    IsProbabilityMeasure (compactHaar K hK) :=
  ⟨compactHaar_univ K hK⟩

/-- Actual multiplication from the parabolic and the supplied compact. -/
def iwasawaMap (x : P × K) : RationalPoint F G.X :=
  (x.1 : RationalPoint F G.X) * (x.2 : RationalPoint F G.X)

theorem continuous_iwasawaMap : Continuous (iwasawaMap χ K) :=
  (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- Push forward the original parabolic and compact Haar measures; no
normalizing coefficient is introduced in this definition. -/
def iwasawaMeasure : Measure (RationalPoint F G.X) :=
  ((parabolicHaar χ K hK).prod (compactHaar K hK)).map (iwasawaMap χ K)

@[simp] theorem iwasawaMeasure_self :
    iwasawaMeasure χ K hK (K : Set (RationalPoint F G.X)) = 1 := by
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpre : iwasawaMap χ K ⁻¹' (K : Set (RationalPoint F G.X)) =
      {p : P | (p : RationalPoint F G.X) ∈ K} ×ˢ (Set.univ : Set K) := by
    ext x
    simp only [Set.mem_preimage, iwasawaMap, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_univ, and_true]
    exact K.toSubgroup.mul_mem_cancel_right x.2.property
  rw [iwasawaMeasure,
    Measure.map_apply (continuous_iwasawaMap χ K).measurable K.isOpen.measurableSet,
    hpre, Measure.prod_prod, compactHaar_univ, mul_one]
  exact subgroupCompactOpenHaar_mass K hK P (isClosed_dynamic_parabolic F G χ)

/-- If the displayed actual Iwasawa factorization holds, its product
pushforward is exactly the original normalized ambient Haar. -/
theorem ambientHaar_eq_iwasawaMeasure
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X)) :
    ambientHaar K hK = iwasawaMeasure χ K hK := by
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hfac : ∀ g : RationalPoint F G.X, ∃ p ∈ P, ∃ k ∈ K.toSubgroup, g = p * k := by
    intro g
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.property, k, k.property, hg⟩
  obtain ⟨c, _, hμ⟩ := CompactFactorization.exists_pos_eq_smul_map_mul_prod
    (ambientHaar K hK) P (isClosed_dynamic_parabolic F G χ) K.toSubgroup hK hfac
    (parabolicHaar χ K hK) (compactHaar K hK)
  change ambientHaar K hK = c • iwasawaMeasure χ K hK at hμ
  have hmass := congrArg
    (fun (ν : Measure (RationalPoint F G.X)) => ν (K : Set (RationalPoint F G.X))) hμ
  have hc : c = 1 := by
    apply ENNReal.coe_injective
    simpa only [ambientHaar_self, Measure.smul_apply, iwasawaMeasure_self,
      ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_one] using hmass.symm
  simpa only [hc, one_smul] using hμ

/-- Nonnegative integration over the actual P,K factors, with both
measures fixed by common-compact mass one. -/
theorem lintegral_eq_parabolic_compact
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(ambientHaar K hK) =
      ∫⁻ p : P, ∫⁻ k : K, f ((p : RationalPoint F G.X) * (k : RationalPoint F G.X))
        ∂(compactHaar K hK) ∂(parabolicHaar χ K hK) := by
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [ambientHaar_eq_iwasawaMeasure χ K hK hPK, iwasawaMeasure,
    lintegral_map hf (continuous_iwasawaMap χ K).measurable]
  exact lintegral_prod _ (hf.comp (continuous_iwasawaMap χ K).measurable).aemeasurable

/-- Canonical Levi-first Iwasawa coordinates, with the precise stability
premise for the normalized parabolic product comparison. -/
theorem lintegral_eq_levi_radical_compact_of_limit_stable
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(ambientHaar K hK) =
      ∫⁻ m : M, ∫⁻ u : U, ∫⁻ k : K,
        f ((m : RationalPoint F G.X) * u * (k : RationalPoint F G.X))
          ∂(compactHaar K hK) ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  rw [lintegral_eq_parabolic_compact χ K hK hPK f hf]
  have hΦ : Measurable (fun p : P => ∫⁻ k : K,
      f ((p : RationalPoint F G.X) * (k : RationalPoint F G.X))
        ∂(compactHaar K hK)) :=
    (hf.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable).lintegral_prod_right'
  exact lintegral_parabolicHaar_of_limit_stable χ K hK hstable _ hΦ

/-- Waldspurger's first nonnegative integration formula in literal
U,M,K order, retaining Iwasawa factorization and compact-limit stability. -/
theorem lintegral_eq_iwasawa_source_order_of_limit_stable
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : P, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(ambientHaar K hK) =
      ∫⁻ u : U, ∫⁻ m : M, inverseLeviModulus χ m *
        ∫⁻ k : K, f ((u : RationalPoint F G.X) * m * (k : RationalPoint F G.X))
          ∂(compactHaar K hK) ∂(leviHaar χ K hK) ∂(radicalHaar χ K hK) := by
  let : LocallyCompactSpace M := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace U := (isClosed_unipotentPoints χ).locallyCompactSpace
  rw [lintegral_eq_levi_radical_compact_of_limit_stable χ K hK hPK hstable f hf]
  let Φ : RationalPoint F G.X → ℝ≥0∞ := fun g =>
    ∫⁻ k : K, f (g * (k : RationalPoint F G.X)) ∂(compactHaar K hK)
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
