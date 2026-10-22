import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Topology.CompactOpen.ConjugationStabilizer
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Representation.Jacquet.PositiveCharacter
import Langlands.Representation.Twist.SmoothProof

open scoped NNReal ENNReal
open MeasureTheory Topology

universe u v

namespace Langlands.HaarModulus

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation on the actual subgroup by an element of its normalizer. -/
def normalizerConj (U : Subgroup G) (g : (Subgroup.normalizer (U : Set G))) : U ≃ₜ* U where
  toFun u := ⟨g * (u : G) * (g : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp g.property u).mp u.property⟩
  invFun u := ⟨(g : G)⁻¹ * (u : G) * g,
    (Subgroup.mem_normalizer_iff''.mp g.property u).mp u.property⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' u v := by ext; simp [mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem normalizerConj_apply (U : Subgroup G) (g : (Subgroup.normalizer (U : Set G))) (u : U) :
    (normalizerConj U g u : G) = g * (u : G) * (g : G)⁻¹ := rfl

@[simp] theorem normalizerConj_symm_apply (U : Subgroup G) (g : (Subgroup.normalizer (U : Set G))) (u : U) :
    ((normalizerConj U g).symm u : G) = (g : G)⁻¹ * (u : G) * g := rfl

@[simp] theorem normalizerConj_one (U : Subgroup G) :
    normalizerConj U 1 = ContinuousMulEquiv.refl U := by
  ext u; simp

theorem normalizerConj_mul (U : Subgroup G) (g h : (Subgroup.normalizer (U : Set G))) :
    normalizerConj U (g * h) = (normalizerConj U h).trans (normalizerConj U g) := by
  ext u; simp [mul_assoc]

local instance subgroupMeasurableSpace (U : Subgroup G) : MeasurableSpace U := borel U
local instance subgroupBorelSpace (U : Subgroup G) : BorelSpace U := ⟨rfl⟩

variable (U : Subgroup G) [LocallyCompactSpace U]

/-- The positive Haar modulus of the actual normalizer action. -/
noncomputable def normalizerCharacter : (Subgroup.normalizer (U : Set G)) →* ℝ≥0ˣ where
  toFun g := Units.mk0 (mulEquivHaarChar (normalizerConj U g))
    (mulEquivHaarChar_pos _).ne'
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul, normalizerConj_mul, mulEquivHaarChar_trans]
    exact mul_comm _ _

@[simp] theorem normalizerCharacter_apply (g : (Subgroup.normalizer (U : Set G))) :
    (normalizerCharacter U g : ℝ≥0) = mulEquivHaarChar (normalizerConj U g) := rfl

@[simp] theorem normalizerCharacter_one : normalizerCharacter U 1 = 1 :=
  (normalizerCharacter U).map_one

@[simp] theorem normalizerCharacter_mul
    (g h : Subgroup.normalizer (U : Set G)) :
    normalizerCharacter U (g * h) = normalizerCharacter U g * normalizerCharacter U h :=
  (normalizerCharacter U).map_mul g h

@[simp] theorem normalizerCharacter_inv (g : Subgroup.normalizer (U : Set G)) :
    normalizerCharacter U g⁻¹ = (normalizerCharacter U g)⁻¹ :=
  map_inv (normalizerCharacter U) g

theorem normalizerCharacter_pos (g : (Subgroup.normalizer (U : Set G))) :
    0 < (normalizerCharacter U g : ℝ≥0) := mulEquivHaarChar_pos _

theorem normalizerCharacter_ne_zero (g : (Subgroup.normalizer (U : Set G))) :
    (normalizerCharacter U g : ℝ≥0) ≠ 0 := (normalizerCharacter_pos U g).ne'

/-- Haar scaling; the factor multiplies the pushforward to recover the measure. -/
theorem normalizerCharacter_smul_map (g : (Subgroup.normalizer (U : Set G))) (μ : Measure U)
    [μ.IsHaarMeasure] [μ.Regular] :
    (normalizerCharacter U g : ℝ≥0) • μ.map (normalizerConj U g) = μ :=
  mulEquivHaarChar_smul_map μ _

/-- The BZ77 1.7 orientation uses the inverse automorphism in the integrand. -/
theorem integral_normalizerConj_symm (g : (Subgroup.normalizer (U : Set G))) (μ : Measure U)
    [μ.IsHaarMeasure] [μ.Regular] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U → E) :
    (∫ u, f ((normalizerConj U g).symm u) ∂μ) =
      (normalizerCharacter U g : ℝ≥0) • ∫ u, f u ∂μ := by
  let e := (normalizerConj U g).toHomeomorph.toMeasurableEquiv
  change (∫ u, f (e.symm u) ∂μ) = _
  rw [← integral_map_equiv e.symm, e.map_symm]
  change (∫ u, f u ∂(μ.comap (normalizerConj U g))) = _
  rw [← mulEquivHaarChar_smul_eq_comap μ (normalizerConj U g)]
  exact integral_smul_nnreal_measure f _

/-- Preservation of a compact open subgroup forces Haar modulus one. -/
theorem normalizerCharacter_eq_one_of_preimage (K : OpenSubgroup U)
    (hK : IsCompact (K : Set U)) (g : Subgroup.normalizer (U : Set G))
    (hg : normalizerConj U g ⁻¹' (K : Set U) = K) :
    normalizerCharacter U g = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts U :=
    ⟨⟨(K : Set U), hK⟩, by simpa only [K.isOpen.interior_eq] using
      (show (K : Set U).Nonempty from ⟨1, K.one_mem⟩)⟩
  have h := mulEquivHaarChar_smul_preimage (Measure.haarMeasure K₀)
    (X := (K : Set U)) (normalizerConj U g)
  rw [hg, show Measure.haarMeasure K₀ (K : Set U) = 1 from Measure.haarMeasure_self] at h
  simp only [ENNReal.smul_def, smul_eq_mul, mul_one] at h
  apply Units.ext
  change mulEquivHaarChar (normalizerConj U g) = 1
  exact_mod_cast h

/-- The actual normalizer Haar character has open kernel. -/
theorem isOpen_ker_normalizerCharacter [NonarchimedeanGroup U] :
    IsOpen ((normalizerCharacter U).ker : Set (Subgroup.normalizer (U : Set G))) := by
  obtain ⟨K, hK, _⟩ := Langlands.compactOpenSubgroupBasis U Set.univ (by simp)
  apply Subgroup.isOpen_mono (H₁ := (compactOpenNormalizerStabilizer U K hK).toSubgroup)
    (H₂ := (normalizerCharacter U).ker) ?_ (compactOpenNormalizerStabilizer U K hK).isOpen
  intro g hg
  apply normalizerCharacter_eq_one_of_preimage U K hK g
  ext u
  exact ((mem_compactOpenNormalizerStabilizer_iff_smul U K hK g).mp hg u).symm

/-- Restriction to any concrete subgroup normalizing U. -/
noncomputable def restrictCharacter (M : Subgroup G) (hMU : M ≤ (Subgroup.normalizer (U : Set G))) : M →* ℝ≥0ˣ :=
  (normalizerCharacter U).comp (Subgroup.inclusion hMU)

@[simp] theorem restrictCharacter_apply (M : Subgroup G) (hMU : M ≤ (Subgroup.normalizer (U : Set G))) (m : M) :
    restrictCharacter U M hMU m = normalizerCharacter U ⟨m, hMU m.property⟩ := rfl

/-- The canonical positive complex half of the restricted modulus. -/
noncomputable def halfCharacter (M : Subgroup G) (hMU : M ≤ (Subgroup.normalizer (U : Set G))) : M →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (restrictCharacter U M hMU))

/-- The canonical inverse half used in Jacquet normalization. -/
noncomputable def inverseHalfCharacter (M : Subgroup G) (hMU : M ≤ (Subgroup.normalizer (U : Set G))) : M →* ℂˣ :=
  Jacquet.inverseHalfCharacter (restrictCharacter U M hMU)

@[simp] theorem halfCharacter_apply (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    (halfCharacter U M hMU m : ℂ) =
      ((NNReal.sqrt (restrictCharacter U M hMU m : ℝ≥0) : ℝ) : ℂ) := rfl

@[simp] theorem inverseHalfCharacter_apply (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    (inverseHalfCharacter U M hMU m : ℂ) =
      (((NNReal.sqrt (restrictCharacter U M hMU m : ℝ≥0) : ℝ) : ℂ))⁻¹ :=
  Jacquet.inverseHalfCharacter_apply _ _

theorem halfCharacter_sq (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    halfCharacter U M hMU m ^ 2 = Jacquet.complexCharacter (restrictCharacter U M hMU) m := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter _) m ^ 2 = _
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

theorem inverseHalfCharacter_sq (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    inverseHalfCharacter U M hMU m ^ 2 =
      (Jacquet.complexCharacter (restrictCharacter U M hMU) m)⁻¹ :=
  Jacquet.inverseHalfCharacter_sq _ _

theorem isOpen_ker_restrictCharacter [NonarchimedeanGroup U] (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((restrictCharacter U M hMU).ker : Set M) :=
  (isOpen_ker_normalizerCharacter U).preimage (continuous_subtype_val.subtype_mk _)

theorem halfCharacter_ker (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    (halfCharacter U M hMU).ker = (restrictCharacter U M hMU).ker := by
  ext m
  simpa only [MonoidHom.mem_ker, Jacquet.inverseHalfCharacter, MonoidHom.inv_apply,
    inv_eq_one, halfCharacter] using
    Jacquet.inverseHalfCharacter_eq_one (restrictCharacter U M hMU) m

theorem isOpen_ker_halfCharacter [NonarchimedeanGroup U] (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((halfCharacter U M hMU).ker : Set M) := by
  rw [halfCharacter_ker]
  exact isOpen_ker_restrictCharacter U M hMU

theorem isOpen_ker_inverseHalfCharacter [NonarchimedeanGroup U] (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((inverseHalfCharacter U M hMU).ker : Set M) :=
  Jacquet.isOpen_ker_inverseHalfCharacter _ (isOpen_ker_restrictCharacter U M hMU)

theorem isSmooth_twist_halfCharacter_iff [NonarchimedeanGroup U] (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ M V) :
    IsSmooth (twist (halfCharacter U M hMU) ρ) ↔ IsSmooth ρ :=
  isSmooth_twist_iff _ ρ (isOpen_ker_halfCharacter U M hMU)

theorem isSmooth_twist_inverseHalfCharacter_iff [NonarchimedeanGroup U] (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ M V) :
    IsSmooth (twist (inverseHalfCharacter U M hMU) ρ) ↔ IsSmooth ρ :=
  isSmooth_twist_iff _ ρ (isOpen_ker_inverseHalfCharacter U M hMU)

end General

section Closed

variable {G : Type u} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  (U : Subgroup G)

section Definitions

variable [IsTopologicalGroup G]

/-- Closed-subgroup specialization supplies the local compactness instance. -/
noncomputable def closedNormalizerCharacter (hU : IsClosed (U : Set G)) :
    Subgroup.normalizer (U : Set G) →* ℝ≥0ˣ :=
  letI := hU.locallyCompactSpace
  normalizerCharacter U

noncomputable def closedRestrictCharacter (hU : IsClosed (U : Set G))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G)) : M →* ℝ≥0ˣ :=
  (closedNormalizerCharacter U hU).comp (Subgroup.inclusion hMU)

noncomputable def closedHalfCharacter (hU : IsClosed (U : Set G))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G)) : M →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (closedRestrictCharacter U hU M hMU))

noncomputable def closedInverseHalfCharacter (hU : IsClosed (U : Set G))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G)) : M →* ℂˣ :=
  Jacquet.inverseHalfCharacter (closedRestrictCharacter U hU M hMU)

/-- With local compactness already available, the closed wrapper is the same character. -/
@[simp] theorem closedNormalizerCharacter_eq [LocallyCompactSpace U]
    (hU : IsClosed (U : Set G)) :
    closedNormalizerCharacter U hU = normalizerCharacter U := rfl

@[simp] theorem closedRestrictCharacter_eq [LocallyCompactSpace U]
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    closedRestrictCharacter U hU M hMU = restrictCharacter U M hMU := rfl

@[simp] theorem closedHalfCharacter_eq [LocallyCompactSpace U]
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    closedHalfCharacter U hU M hMU = halfCharacter U M hMU := rfl

@[simp] theorem closedInverseHalfCharacter_eq [LocallyCompactSpace U]
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    closedInverseHalfCharacter U hU M hMU = inverseHalfCharacter U M hMU := rfl

end Definitions

section Openness

variable [NonarchimedeanGroup G]

theorem isOpen_ker_closedNormalizerCharacter
    (hU : IsClosed (U : Set G)) :
    IsOpen ((closedNormalizerCharacter U hU).ker : Set (Subgroup.normalizer (U : Set G))) := by
  let := hU.locallyCompactSpace
  exact isOpen_ker_normalizerCharacter U

theorem isOpen_ker_closedRestrictCharacter
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((closedRestrictCharacter U hU M hMU).ker : Set M) := by
  let := hU.locallyCompactSpace
  exact isOpen_ker_restrictCharacter U M hMU

theorem isOpen_ker_closedHalfCharacter
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((closedHalfCharacter U hU M hMU).ker : Set M) := by
  let := hU.locallyCompactSpace
  exact isOpen_ker_halfCharacter U M hMU

theorem isOpen_ker_closedInverseHalfCharacter
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    IsOpen ((closedInverseHalfCharacter U hU M hMU).ker : Set M) := by
  let := hU.locallyCompactSpace
  exact isOpen_ker_inverseHalfCharacter U M hMU

theorem isSmooth_twist_closedHalfCharacter_iff
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ M V) :
    IsSmooth (twist (closedHalfCharacter U hU M hMU) ρ) ↔ IsSmooth ρ :=
  isSmooth_twist_iff _ ρ (isOpen_ker_closedHalfCharacter U hU M hMU)

theorem isSmooth_twist_closedInverseHalfCharacter_iff
    (hU : IsClosed (U : Set G)) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ M V) :
    IsSmooth (twist (closedInverseHalfCharacter U hU M hMU) ρ) ↔ IsSmooth ρ :=
  isSmooth_twist_iff _ ρ (isOpen_ker_closedInverseHalfCharacter U hU M hMU)

end Openness

end Closed

end Langlands.HaarModulus
