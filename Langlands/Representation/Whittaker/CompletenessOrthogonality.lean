import Langlands.Representation.Whittaker.CompletenessPairing
import Langlands.Representation.Whittaker.CompletenessUnlinkedBase
import Langlands.Representation.RankinSelberg.PairLFactor
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters
import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof

/-!
# Whittaker completeness: orthogonality to a representation

A standard-character function `H` is orthogonal to a representation `π` when its
pairing with every inverse-character Whittaker function of `π` vanishes. This is
the hypothesis of the supercuspidal product completeness statement, one product
at a time. The module proves that orthogonality is invariant under equivalence,
passes to quotients, follows from the hypothesis of Jacquet–Shalika 1985,
Lemma (3.2), after the change of character `ψ ↦ ψ⁻¹`, and passes from the
deformed two-block representations `ρ_u` of JPSS 1983, Section (4.5), with `u`
real near `0`, to `ρ_0`.
-/

noncomputable section

namespace Langlands.Whittaker.CompletenessOrthogonality

open MeasureTheory HarmonicAnalysis GeneralLinear RankinSelberg Filter
open scoped _root_.Topology

universe uF uV uV₂ uW uX

section General

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]

/-- `H` is orthogonal for `μ` to `π`: its pairing with every inverse-character
Whittaker function of `π` vanishes. -/
def Orthogonal (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F))
    (H : WhittakerFunctions ψ n) (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Prop :=
  ∀ f ∈ inverseWhittakerSet ψ n π, ∫ q, whittakerProductIntegrand ψ H f q ∂μ = 0

variable {ψ : UnitaryAdditiveCharacter F} {μ : Measure (LeftUnipotentQuotient n F)}
  {H : WhittakerFunctions ψ n}

/-- Orthogonality in the form used by `SupercuspidalProductCompletenessStatement`:
every functional and every vector of its coefficient model. -/
theorem orthogonal_iff_forall_coefficientModel
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} :
    Orthogonal ψ μ H π ↔ ∀ (ℓ' : glInverseFunctionals ψ n π)
      (f : (coefficientModel π ℓ').toSubmodule),
        ∫ q, whittakerProductIntegrand ψ H f.val q ∂μ = 0 := by
  constructor
  · intro h ℓ' f
    exact h f.val ⟨ℓ', f.property⟩
  · rintro h f ⟨ℓ', hf⟩
    exact h ℓ' ⟨f, hf⟩

/-- Orthogonality passes to quotients. -/
theorem Orthogonal.of_surjective {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f) (h : Orthogonal ψ μ H π) :
    Orthogonal ψ μ H π₂ :=
  fun w hw => h w (inverseWhittakerSet_subset_of_surjective ψ f hf hw)

/-- Orthogonality is invariant under equivalence. -/
theorem orthogonal_iff_of_equiv {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂} (φ : π.Equiv π₂) :
    Orthogonal ψ μ H π ↔ Orthogonal ψ μ H π₂ := by
  unfold Orthogonal
  rw [inverseWhittakerSet_eq_of_equiv ψ φ]

omit [MeasurableSpace (LeftUnipotentQuotient n F)] in
/-- The pairing with the zero function is the zero function. -/
theorem whittakerProductIntegrand_zero (ψ : UnitaryAdditiveCharacter F)
    (H : WhittakerFunctions ψ n) : whittakerProductIntegrand ψ H 0 = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change H.val g * 0 = 0
    exact mul_zero _

end General

section Scale

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The two pairings `∫ W H` (for `ψ`) and `∫ H W` (for `ψ⁻¹ = ψ.scale (-1)`) have the
same integrand. -/
theorem whittakerProductIntegrand_scale_neg_one (ψ : UnitaryAdditiveCharacter F)
    (H : InverseWhittakerFunctions ψ n) (f : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    whittakerProductIntegrand ψ (InducedTailIntermediate.scaledInverseAsStandard ψ f) H =
      whittakerProductIntegrand (ψ.scale (-1))
        (InducedTailIntermediate.inverseAsScaledStandard ψ H) f := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change f.val g * H.val g = H.val g * f.val g
    exact mul_comm _ _

/-- The invariance and support hypotheses of Jacquet–Shalika 1985, Lemma (3.2), on an
inverse-character function `H` make it a compact Whittaker test function for
`ψ⁻¹ = ψ.scale (-1)`. -/
theorem isCompactWhittakerTestFunction_inverseAsScaledStandard
    (ψ : UnitaryAdditiveCharacter F) (H : InverseWhittakerFunctions ψ n)
    (hK : ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      ∀ g k, k ∈ K → H.val (g * k) = H.val g)
    (hC : ∃ C : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C ∧
      ∀ g, H.val g ≠ 0 → ∃ u : upperUnipotent (n + 1) F, ∃ c ∈ C, g = u.val * c) :
    IsCompactWhittakerTestFunction (ψ.scale (-1)) n
      (InducedTailIntermediate.inverseAsScaledStandard ψ H) := by
  refine ⟨hK, ?_⟩
  obtain ⟨C, hCc, hCs⟩ := hC
  refine ⟨C, hCc, fun g hg => ?_⟩
  obtain ⟨u, c, hc, rfl⟩ := hCs g hg
  exact ⟨u, c, hc, rfl⟩

/-- An inverse-character function `H` orthogonal, in the sense of Jacquet–Shalika 1985,
Lemma (3.2), to every standard Whittaker function of `π` is orthogonal to `π` as a
standard function for `ψ⁻¹ = ψ.scale (-1)`. -/
theorem orthogonal_scale_neg_one_of_forall [MeasurableSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F))
    (H : InverseWhittakerFunctions ψ n)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hH : ∀ (ℓ : glFunctionals ψ n π) (w : (coefficientModel π ℓ).toSubmodule),
      ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0) :
    Orthogonal (ψ.scale (-1)) μ (InducedTailIntermediate.inverseAsScaledStandard ψ H) π := by
  intro f hf
  obtain ⟨ℓ, hℓ⟩ := InducedTailIntermediate.scaledInverseAsStandard_mem ψ π hf
  rw [← whittakerProductIntegrand_scale_neg_one]
  exact hH ℓ ⟨_, hℓ⟩

end Scale

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance completenessOrthogonalityTopologicalSpace : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance completenessOrthogonalityValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance completenessOrthogonalityIsNonarchimedeanLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

/-- The hypothesis of Jacquet–Shalika 1985, Lemma (3.2), for generic representations on
carriers in `Type uV`, gives orthogonality at `ψ.scale (-1)` to every generic
representation, in any carrier universe. -/
theorem orthogonal_scale_neg_one_of_isGeneric (ψ : UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F.Carrier)]
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) (H : InverseWhittakerFunctions ψ n)
    (hH : ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsGeneric ψ n π →
        ∀ (ℓ : glFunctionals ψ n π) (w : (coefficientModel π ℓ).toSubmodule),
          ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0)
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) X)
    (hπ : IsGeneric ψ n π) :
    Orthogonal (ψ.scale (-1)) μ (InducedTailIntermediate.inverseAsScaledStandard ψ H) π :=
  orthogonal_scale_neg_one_of_forall ψ μ H π fun ℓ w =>
    forall_coefficientModel_of_isGeneric.{uF, uV} ψ n
      (fun f => ∫ x, whittakerProductIntegrand ψ f H x ∂μ = 0) hH π hπ ℓ w

/-- The deformation step. Let `ρ_u` be the lower induction of two blocks of Whittaker
type, the first twisted by `|det|^u`. If a compact Whittaker test function `H` is
orthogonal to `ρ_u` for all real `u ≠ 0` near `0`, it is orthogonal to `ρ_0`. Each
Whittaker function of `ρ_0` is the value at `0` of an entire family of Whittaker
functions of `ρ_u` with one open right stabilizer (`twoBlockWhittakerDeformation`),
and the pairing with `H` is continuous along such families. -/
theorem orthogonal_twoBlockDeformedInduced_zero (ψ : UnitaryAdditiveCharacter F.Carrier)
    {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
    [OpensMeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
    {H : WhittakerFunctions ψ t} (hH : IsCompactWhittakerTestFunction ψ t H)
    (μ : Measure (LeftUnipotentQuotient t F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    (hev : ∀ᶠ u : ℝ in 𝓝[≠] 0, Orthogonal ψ μ H (twoBlockDeformedInduced F m h σ (u : ℂ))) :
    Orthogonal ψ μ H (twoBlockDeformedInduced F m h σ 0) := by
  rintro f ⟨ℓ₀, v₀, rfl⟩
  by_cases hℓ₀ : ℓ₀.val = 0
  · have hz : (coefficientMap (twoBlockDeformedInduced F m h σ 0) ℓ₀).toLinearMap v₀ = 0 := by
      apply Subtype.ext
      funext g
      change ℓ₀.val _ = 0
      rw [hℓ₀]
      rfl
    rw [hz, whittakerProductIntegrand_zero]
    exact integral_zero _ _
  obtain ⟨Wu, h0, hu, ⟨K, hKo, -, hK⟩, han⟩ :=
    twoBlockWhittakerDeformation p F ψ t m h σ hσ ℓ₀ hℓ₀ v₀
  choose ℓ _ v hv using hu
  let fu : ℝ → InverseWhittakerFunctions ψ t := fun u =>
    coefficientMap (twoBlockDeformedInduced F m h σ (u : ℂ)) (ℓ u) (v u)
  have hfu : ∀ (u : ℝ) g, (fu u).val g = Wu u g := fun u g => (hv u g).symm
  let K' : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨K, hKo⟩
  refine CompletenessPairing.integral_whittakerProductIntegrand_eq_zero_of_tendsto ψ hH μ
    (l := 𝓝[≠] (0 : ℝ)) fu _ K' ?_ ?_ ?_ ?_
  · intro u g k hk
    rw [hfu, hfu]
    exact hK u g ⟨k, hk⟩
  · intro g k hk
    change ℓ₀.val _ = ℓ₀.val _
    rw [← h0, ← h0]
    exact hK 0 g ⟨k, hk⟩
  · intro g
    have hofReal : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      simpa using this
    have hlim := ((han g 0).continuousAt.tendsto).comp hofReal
    change Tendsto (fun u : ℝ => (fu u).val g) _ (𝓝 (ℓ₀.val _))
    rw [← h0]
    refine hlim.congr fun u => ?_
    exact (hfu u g).symm
  · refine hev.mono fun u hu => hu _ ⟨ℓ u, v u, rfl⟩

end Padic

end Langlands.Whittaker.CompletenessOrthogonality
