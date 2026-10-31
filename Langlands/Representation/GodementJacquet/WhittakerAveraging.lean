import Langlands.Representation.GodementJacquet.LeftAveraging
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof
import Langlands.Group.GL.NormalizedCharacter

/-!
# Left compact averaging of Whittaker model functions

JPS (1979), equations (3.1.3)–(3.1.4): averaging a Whittaker function on the
left over a compact open subgroup that fixes the test function gives a
bi-smooth matrix coefficient of the model with the same full-matrix integral.
Consequently `I₃ ⊆ I₂` for the actual coefficient model.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg Topology
open scoped ENNReal NNReal Pointwise

universe uF uV uG

section Translation

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul G]
  (μ : Measure G) [μ.IsMulRightInvariant]

/-- Right translation by an element of a measurable subgroup preserves set integrals
over that subgroup. -/
theorem setIntegral_mul_right_of_mem (K : Subgroup G) (hKm : MeasurableSet (K : Set G))
    {k : G} (hk : k ∈ K) (f : G → ℂ) :
    ∫ x in (K : Set G), f (x * k) ∂μ = ∫ x in (K : Set G), f x ∂μ := by
  have hpre : (fun x => x * k) ⁻¹' (K : Set G) = K := by
    ext x
    simp [K.mul_mem_cancel_right hk]
  have h := (measurePreserving_mul_right μ k).restrict_preimage hKm
  rw [hpre] at h
  exact h.integral_comp (measurableEmbedding_mulRight k) f

end Translation

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance averagingTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance averagingValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance averagingLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance averagingMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance averagingBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance averagingSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance averagingSigmaCompact (n : ℕ) : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)

variable {n : ℕ}

/-- A full-matrix test function is invariant under left multiplication by every
element of some neighborhood of the identity. -/
theorem exists_nhds_matrixTest_invariant (Φ : MatrixTestFunction n F.Carrier) :
    ∃ U ∈ 𝓝 (1 : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ g ∈ U, ∀ M, Φ (g.val * M) = Φ M := by
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let X := Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier
  have hcont : Continuous fun z : G × X => z.1.val * z.2 :=
    (Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd
  have hlc : IsLocallyConstant fun z : G × X => Φ (z.1.val * z.2) - Φ z.2 :=
    IsLocallyConstant.comp₂ ((SchwartzBruhat.locallyConstant Φ).comp_continuous hcont)
      ((SchwartzBruhat.locallyConstant Φ).comp_continuous continuous_snd) (· - ·)
  have hsub : ({1} : Set G) ×ˢ tsupport (Φ : X → ℂ) ⊆
      {z : G × X | Φ (z.1.val * z.2) - Φ z.2 = 0} := by
    rintro ⟨g, M⟩ ⟨hg, -⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show Φ ((1 : G).val * M) - Φ M = 0
    rw [Units.val_one, Matrix.one_mul, sub_self]
  obtain ⟨u, v, hu, -, h1u, hSv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (SchwartzBruhat.hasCompactSupport Φ).isCompact (hlc.isOpen_fiber 0) hsub
  have hun : u ∈ 𝓝 (1 : G) := hu.mem_nhds (h1u rfl)
  have key : ∀ h ∈ u, ∀ N ∈ tsupport (Φ : X → ℂ), Φ (h.val * N) = Φ N := by
    intro h hh N hN
    have hm : Φ (h.val * N) - Φ N = 0 := huv (Set.mk_mem_prod hh (hSv hN))
    exact sub_eq_zero.mp hm
  refine ⟨u ∩ u⁻¹, Filter.inter_mem hun (inv_mem_nhds_one G hun), ?_⟩
  rintro g ⟨hgu, hgu'⟩ M
  by_cases hM : M ∈ tsupport (Φ : X → ℂ)
  · exact key g hgu M hM
  by_cases hgM : g.val * M ∈ tsupport (Φ : X → ℂ)
  · have hinv := key g⁻¹ (Set.mem_inv.mp hgu') _ hgM
    have e : (g⁻¹ : G).val * (g.val * M) = M := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [e] at hinv
    exact hinv.symm
  · rw [image_eq_zero_of_notMem_tsupport hM, image_eq_zero_of_notMem_tsupport hgM]

/-- A compact open subgroup of `GL_(n+1)` fixing a full-matrix test function under
left multiplication and lying in the kernel of the normalized determinant norm. -/
theorem exists_compactOpen_matrixTest_invariant (Φ : MatrixTestFunction n F.Carrier) :
    ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
      ∀ k ∈ K, (∀ M, Φ (k.val * M) = Φ M) ∧
        normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 := by
  obtain ⟨U, hU, hΦ⟩ := exists_nhds_matrixTest_invariant F Φ
  let T := F.canonicalTopologicalData
  have hker : ((T.determinantNorm (n + 1)).ker :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∈ 𝓝 1 :=
    (T.isOpen_ker_determinantNorm (n + 1)).mem_nhds (one_mem _)
  obtain ⟨L, hLc, hLU⟩ := T.generalLinearCompactOpen (n + 1) _ (Filter.inter_mem hU hker)
  refine ⟨L, hLc, fun k hk => ⟨hΦ k (hLU hk).1, ?_⟩⟩
  have h : T.determinantNorm (n + 1) k = 1 := (hLU hk).2
  have h1 : ((T.determinantNorm (n + 1) k : ℝ≥0) : ℝ) = 1 := by
    rw [h]
    rfl
  rw [T.determinantNorm_coe] at h1
  exact h1

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- The integral of model functions over a compact set, as a linear functional on
the model. -/
def modelSetIntegral (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :
    Module.Dual ℂ (glCoefficientModel ψ n σ ℓ).toSubmodule where
  toFun W := ∫ k in (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
    glModelFunction ψ n σ ℓ W k ∂(generalLinearHaar F.Carrier n)
  map_add' W₁ W₂ := by
    have h₁ := (glModelFunction_continuous ψ n σ hσ ℓ W₁).continuousOn.integrableOn_compact'
      (μ := generalLinearHaar F.Carrier n) hK K.isOpen.measurableSet
    have h₂ := (glModelFunction_continuous ψ n σ hσ ℓ W₂).continuousOn.integrableOn_compact'
      (μ := generalLinearHaar F.Carrier n) hK K.isOpen.measurableSet
    rw [← integral_add h₁ h₂]
    rfl
  map_smul' c W := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    rfl

/-- Integration over a compact open subgroup is a smooth functional on the model:
it is fixed by that subgroup, by right invariance of the Haar measure. -/
def modelSetIntegralDual (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :
    SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  ⟨modelSetIntegral F ψ σ hσ ℓ K hK, by
    refine ⟨K, ?_⟩
    rw [fixedVectors, Representation.mem_invariants]
    intro k
    apply LinearMap.ext
    intro W
    change ∫ x in (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
        glModelFunction ψ n σ ℓ W (x * (k : Langlands.GeneralLinear (n + 1) F.Carrier)⁻¹)
          ∂(generalLinearHaar F.Carrier n) =
      ∫ x in (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
        glModelFunction ψ n σ ℓ W x ∂(generalLinearHaar F.Carrier n)
    exact setIntegral_mul_right_of_mem (generalLinearHaar F.Carrier n) K.toSubgroup
      K.isOpen.measurableSet (K.toSubgroup.inv_mem k.2) _⟩

/-- JPS (1979) (3.1.3)–(3.1.4): every rational value of a Whittaker integral on
the actual model is a rational value of a bi-smooth matrix-coefficient integral of
the model representation. -/
theorem whittakerRationalValues_subset (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ) :
    whittakerRationalValues F ψ σ ℓ ⊆
      matrixRationalValues F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) := by
  rintro R ⟨Φ, w, hconv, hrat⟩
  obtain ⟨K, hKc, hK⟩ := exists_compactOpen_matrixTest_invariant F Φ
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let μ := generalLinearHaar F.Carrier n
  let abv := normalizedAbsoluteValue F.canonicalTopologicalData
  let W := glModelFunction ψ n σ ℓ w
  have hKm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hKfin : μ (K : Set G) ≠ ∞ := hKc.measure_lt_top.ne
  have hKpos : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hreal : (μ.real (K : Set G) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hKpos, hKfin⟩
  let Λ := modelSetIntegralDual F ψ σ hσ ℓ K hKc
  let v : smoothVectors (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) := ⟨w, glModel_isSmooth ψ n σ hσ ℓ w⟩
  let c : ℂ := (μ.real (K : Set G) : ℂ)⁻¹
  let f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
    c • ⟨biSmoothCoefficient _ Λ v, Submodule.subset_span ⟨Λ, v, rfl⟩⟩
  have hf : ∀ g, f.val g = c * ∫ x in (K : Set G), W (x * g) ∂μ := fun g => rfl
  have key : ∀ s : ℂ, GodementJacquet.MatrixConverges abv μ Φ s W →
      GodementJacquet.MatrixConverges abv μ Φ s f.val ∧
        GodementJacquet.matrixIntegral abv μ Φ s f.val =
          GodementJacquet.matrixIntegral abv μ Φ s W := by
    intro s hs
    let a : G → ℂ := fun g => Φ g.val * determinantWeight abv g s
    have ha : ∀ x ∈ (K : Set G), ∀ g, a (x * g) = a g := by
      intro x hx g
      obtain ⟨hΦx, hdet⟩ := hK x hx
      have e : (x * g).val = x.val * g.val := rfl
      have hdet' : abv x.val.det = 1 := hdet
      show Φ (x * g).val * determinantWeight abv (x * g) s =
        Φ g.val * determinantWeight abv g s
      rw [determinantWeight, determinantWeight, e, hΦx, Matrix.det_mul, AbsoluteValue.map_mul,
        hdet', one_mul]
    have hint : Integrable (fun g => a g * W g) μ := by
      refine (hs : Integrable (GodementJacquet.matrixIntegrand abv Φ s W) μ).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp only [GodementJacquet.matrixIntegrand, a]
      ring
    obtain ⟨h1, h2⟩ := leftAverage_integral μ (K : Set G) hKm hKfin a W ha hint
    have hpt : GodementJacquet.matrixIntegrand abv Φ s f.val =
        fun g => c * (a g * ∫ x in (K : Set G), W (x * g) ∂μ) := by
      funext g
      simp only [GodementJacquet.matrixIntegrand, hf, a]
      ring
    have hW : GodementJacquet.matrixIntegrand abv Φ s W = fun g => a g * W g := by
      funext g
      simp only [GodementJacquet.matrixIntegrand, a]
      ring
    refine ⟨?_, ?_⟩
    · change Integrable (GodementJacquet.matrixIntegrand abv Φ s f.val) μ
      rw [hpt]
      exact h1.const_mul c
    · change ∫ g, GodementJacquet.matrixIntegrand abv Φ s f.val g ∂μ =
        ∫ g, GodementJacquet.matrixIntegrand abv Φ s W g ∂μ
      rw [hpt, hW, integral_const_mul, h2, ← mul_assoc, inv_mul_cancel₀ hreal, one_mul]
  obtain ⟨a₁, ha₁⟩ := hconv
  obtain ⟨a₂, ha₂⟩ := hrat
  refine ⟨Φ, f, ⟨a₁, fun s hs => (key _ (ha₁ s hs)).1⟩, max a₁ a₂, fun s hs => ?_⟩
  obtain ⟨hd, he⟩ := ha₂ s (lt_of_le_of_lt (le_max_right _ _) hs)
  refine ⟨hd, ?_⟩
  rw [← he]
  exact (key _ (ha₁ s (lt_of_le_of_lt (le_max_left _ _) hs))).2

/-- `I₃ ⊆ I₂` for the actual coefficient model of a smooth representation. -/
theorem jpssI3_le_jpssI2 (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ) :
    jpssI3 F ψ σ ℓ ≤
      jpssI2 F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) :=
  Submodule.span_mono (whittakerRationalValues_subset F ψ σ hσ ℓ)

end Padic

end Langlands.GodementJacquet
