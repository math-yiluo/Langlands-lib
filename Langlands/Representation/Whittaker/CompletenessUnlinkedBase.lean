import Langlands.Representation.Whittaker.CompletenessStatement
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.Whittaker.Transport

/-!
# Whittaker completeness: the unlinked supercuspidal base case

Let `τ_1, …, τ_k` be smooth irreducible supercuspidal representations of the
diagonal blocks of a standard block shape, with no pair `τ_j ≅ ν τ_i`
(`ν = |det|`). Their normalized product is irreducible: these are one-term
segment socles with an unlinked multisegment (Zelevinsky 1980, Theorem 4.2). It
is also generic. A function `H` orthogonal to the Whittaker functions of every
generic representation with carrier in one fixed universe is therefore
orthogonal to every Whittaker function of that product. This is the base case
of the reduction of Jacquet–Shalika 1985, Lemma (3.2), to products of
supercuspidals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The cuspidal datum, Zelevinsky's element of `𝒞`, of a smooth irreducible
supercuspidal representation of `GL_n(F)` with `n > 0`. -/
def supercuspidalDatum {n : ℕ} (hn : 0 < n) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear n F.Carrier) W)
    (hs : letI := T.topology; IsSmooth τ) (hirr : Representation.IsIrreducible τ)
    (hsc : letI := T.topology; GeneralLinear.IsSupercuspidal τ) :
    CuspidalDatum.{uW, uF} T :=
  letI := T.topology
  ⟨n, hn, GeneralLinear.SupercuspidalRep.isoClass (F := F.Carrier) (n := n)
    (⟨SmoothRep.of τ hs, hirr, hsc⟩ :
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n))⟩

@[simp]
theorem supercuspidalDatum_rank {n : ℕ} (hn : 0 < n) {W : Type uW} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (GeneralLinear n F.Carrier) W)
    (hs : letI := T.topology; IsSmooth τ) (hirr : Representation.IsIrreducible τ)
    (hsc : letI := T.topology; GeneralLinear.IsSupercuspidal τ) :
    (T.supercuspidalDatum hn τ hs hirr hsc).rank = n := rfl

/-- The datum of `τ ⊗ |det|^s` is the twist `ν^s` of the datum of `τ`. -/
theorem supercuspidalDatum_twist {n : ℕ} (hn : 0 < n) {W : Type uW} [AddCommGroup W]
    [Module ℂ W] (s : ℝ) (τ : Representation ℂ (GeneralLinear n F.Carrier) W)
    (hs : letI := T.topology; IsSmooth τ) (hirr : Representation.IsIrreducible τ)
    (hsc : letI := T.topology; GeneralLinear.IsSupercuspidal τ)
    (hs' : letI := T.topology; IsSmooth (Langlands.twist (T.determinantPowerCharacter n s) τ))
    (hirr' : Representation.IsIrreducible (Langlands.twist (T.determinantPowerCharacter n s) τ))
    (hsc' : letI := T.topology;
      GeneralLinear.IsSupercuspidal (Langlands.twist (T.determinantPowerCharacter n s) τ)) :
    T.supercuspidalDatum hn (Langlands.twist (T.determinantPowerCharacter n s) τ) hs' hirr' hsc' =
      (T.supercuspidalDatum hn τ hs hirr hsc).twist s := rfl

/-- Two one-term segments `{ρ}` and `{σ}` are linked only if `σ = ν ρ` or `ρ = ν σ`. -/
theorem eq_twist_one_of_singletonSegment_isLinked {ρ σ : CuspidalDatum.{uV, uF} T}
    (h : (T.singletonSegment ρ).IsLinked (T.singletonSegment σ)) :
    σ = ρ.twist 1 ∨ ρ = σ.twist 1 := by
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF, uV} F T
  have key : ∀ {ρ σ : CuspidalDatum.{uV, uF} T},
      (T.singletonSegment ρ).Precedes (T.singletonSegment σ) → σ = ρ.twist 1 := by
    intro ρ σ hp
    obtain ⟨k, -, he⟩ := hp.2
    change σ = ρ.twist (k : ℝ) at he
    have hΔ : (T.singletonSegment ρ).HasIntegralCoordinates ρ 0 0 :=
      ⟨by simp [singletonSegment], by simp [singletonSegment]⟩
    have hΓ : (T.singletonSegment σ).HasIntegralCoordinates ρ k k :=
      ⟨by simpa [singletonSegment] using he, by simp [singletonSegment]⟩
    obtain ⟨h1, h2, -⟩ := (hΔ.precedes_iff hfree hΓ).mp hp
    have hk : k = 1 := by omega
    subst hk
    simpa using he
  rcases h.precedes_or_precedes with hp | hp
  · exact Or.inl (key hp)
  · exact Or.inr (key hp)

/-- A family of cuspidal data with no `ρ_j = ν ρ_i` gives an unlinked multisegment
of one-term segments. -/
theorem SegmentProductDatum.ofCuspidals_isUnlinked {k n : ℕ}
    (ρ : Fin k → CuspidalDatum.{max uF uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := (ρ i).rank))
    (hρ : ∀ i j, ρ j ≠ (ρ i).twist 1) :
    (SegmentProductDatum.ofCuspidals T ρ h A).multisegment.IsUnlinked := by
  intro Δ₁ hΔ₁ Δ₂ hΔ₂ hlink
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΔ₁)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΔ₂)
  rcases T.eq_twist_one_of_singletonSegment_isLinked hlink with he | he
  · exact hρ i j he
  · exact hρ j i he

/-- BZ77 Theorem 4.2 for unbundled blocks: if no block datum is `ν` times another,
the normalized product of smooth irreducible supercuspidal blocks is irreducible.
The proof views the blocks as one-term segment socles and applies Ze80 Theorem 4.2. -/
theorem isIrreducible_normalizedProductInduced_of_unlinked {t : ℕ}
    (B : GeneralLinear.BlockShape (t + 1))
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hs : letI := T.topology; ∀ i, IsSmooth (τ i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : letI := T.topology; ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hunl : ∀ i j, T.supercuspidalDatum (B.positive j) (τ j) (hs j) (hirr j) (hsc j) ≠
      (T.supercuspidalDatum (B.positive i) (τ i) (hs i) (hirr i) (hsc i)).twist 1) :
    Representation.IsIrreducible (T.normalizedProductInduced B τ) := by
  let := T.topology
  let A₀ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i) :=
    fun i => ⟨SmoothRep.of (τ i) (hs i), hirr i, hsc i⟩
  let ρ : Fin B.length → CuspidalDatum.{max uF uW, uF} T :=
    fun i => (T.supercuspidalDatum (B.positive i) (τ i) (hs i) (hirr i) (hsc i)).universeLift
  let A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uW}
      (F := F.Carrier) (n := (ρ i).rank) :=
    fun i => GeneralLinear.SupercuspidalRep.universeLift (A₀ i)
  have hA : ∀ i, (ρ i).IsRepresentedBy (A i) := fun i => rfl
  have hρ : ∀ i j, ρ j ≠ (ρ i).twist 1 := by
    intro i j he
    rw [← CuspidalDatum.universeLift_twist] at he
    exact hunl i j (CuspidalDatum.universeLift_injective he)
  let d := SegmentProductDatum.ofCuspidals T ρ B.sum_eq A
  have hd : Representation.IsIrreducible d.induced.representation :=
    Classification.unlinkedSegmentSocleProductIrreducible.{uF, max uF uW} F T t d
      (SegmentProductDatum.ofCuspidals_hasSegmentSocles T ρ B.sum_eq A hA)
      (SegmentProductDatum.ofCuspidals_isUnlinked T ρ B.sum_eq A hρ)
  let e₁ : (T.normalizedProductInduced B τ).Equiv
      (T.normalizedProductInduced B (fun i => (A i).obj.representation)) :=
    T.normalizedProductInducedEquiv B
      (fun i => GeneralLinear.SupercuspidalRep.universeLiftEquiv (A₀ i))
  let e₂ : d.induced.representation.Equiv
      (T.cuspidalProductInduced ρ B.sum_eq A).representation :=
    SmoothRep.equivOfIso (SegmentProductDatum.ofCuspidalsInducedIso T ρ B.sum_eq A)
  exact (Weil.IsomorphismInvariance.irreducible_iff (e₁.trans e₂.symm)).mpr hd

end Langlands.PadicField.TopologicalData

namespace Langlands.Whittaker

open MeasureTheory HarmonicAnalysis GeneralLinear RankinSelberg

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

/-- The cuspidal datum of the block `τ a` of `GL_(m a + 1)(F)`, for the canonical
structures of `F`. -/
def blockDatum {k : ℕ} {m : Fin k → ℕ}
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)) (a : Fin k) :
    PadicField.TopologicalData.CuspidalDatum.{uW, uF} F.canonicalTopologicalData :=
  F.canonicalTopologicalData.supercuspidalDatum (Nat.succ_pos (m a)) (τ a) (hs a) (hirr a)
    (hsc a)

@[simp]
theorem blockDatum_rank {k : ℕ} {m : Fin k → ℕ}
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i)) (a : Fin k) :
    (blockDatum τ hs hirr hsc a).rank = m a + 1 := rfl

/-- P4a. If no block datum is `ν` times another, the normalized product of smooth
irreducible supercuspidal blocks is irreducible. -/
theorem isIrreducible_canonicalNormalizedProductInduced_of_unlinked {t k : ℕ}
    (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hunl : ∀ a b, blockDatum τ hs hirr hsc a ≠ (blockDatum τ hs hirr hsc b).twist 1) :
    Representation.IsIrreducible
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) :=
  F.canonicalTopologicalData.isIrreducible_normalizedProductInduced_of_unlinked
    (succBlockShape m h) τ hs hirr hsc (fun i j => hunl j i)

/-- The normalized product of irreducible supercuspidal blocks is generic once it is
irreducible: it is admissible with a one-dimensional space of standard Whittaker
functionals by `normalizedProductWhittakerType`, the blocks being of Whittaker type
by the supercuspidal Kirillov theorem. -/
theorem isGeneric_canonicalNormalizedProductInduced
    (ψ : UnitaryAdditiveCharacter F.Carrier) {t k : ℕ} (m : Fin k → ℕ)
    (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hprod : Representation.IsIrreducible
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ)) :
    IsGeneric ψ t (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) := by
  have hW : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) := fun i =>
    isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov (hsc i) (hirr i)
  have hP := normalizedProductWhittakerType p F ψ t k m h τ hW
  refine ⟨hprod, hP.1, ?_⟩
  obtain ⟨L⟩ := hP.2.2
  refine ⟨L.symm 1, fun h0 => one_ne_zero (L.symm.injective ?_)⟩
  rw [map_zero]
  exact Subtype.ext h0

/-- A property of standard Whittaker functions that holds on every Whittaker model
of every generic representation with carrier in `Type uV` holds on every
Whittaker model of every generic representation, in any carrier universe: an
irreducible smooth representation has an equivalent realization in `Type uV`,
and equivalent representations have the same coefficient models. -/
theorem forall_coefficientModel_of_isGeneric
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Φ : WhittakerFunctions ψ n → Prop)
    (hΦ : ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsGeneric ψ n π →
        ∀ (ℓ : glFunctionals ψ n π) (w : (coefficientModel π ℓ).toSubmodule), Φ w.val)
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) X)
    (hπ : IsGeneric ψ n π) (ℓ : glFunctionals ψ n π)
    (w : (coefficientModel π ℓ).toSubmodule) : Φ w.val := by
  obtain ⟨σ, -, ⟨e⟩⟩ := padicIrreducibleSmoothSmallRealization.{uF, uX, uV} p F
    F.canonicalTopologicalData (n + 1) (SmoothRep.of π hπ.2.1.1) hπ.1
  have hσ : IsGeneric ψ n σ.representation := (isGeneric_iff_of_equiv ψ n e).mp hπ
  have hM : coefficientModel σ.representation (functionalPullback e.symm ℓ) =
      coefficientModel π ℓ :=
    coefficientModel_functionalPullback e.symm ℓ
  refine hΦ σ σ.representation hσ (functionalPullback e.symm ℓ) ⟨w.val, ?_⟩
  rw [hM]
  exact w.property

/-- P4b. If the normalized product of irreducible supercuspidal blocks is irreducible,
a function `H` orthogonal, for a measure `μ` on `N \ GL_(t+1)`, to every standard
Whittaker function of every generic representation with carrier in `Type uV` is
orthogonal to every standard Whittaker function of that product. -/
theorem integral_whittakerProductIntegrand_canonicalNormalizedProductInduced_eq_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) {t k : ℕ} (m : Fin k → ℕ)
    (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hprod : Representation.IsIrreducible
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
    [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
    (μ : Measure (LeftUnipotentQuotient t F.Carrier)) (H : InverseWhittakerFunctions ψ t)
    (hH : ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) V),
      IsGeneric ψ t π →
        ∀ (ℓ : glFunctionals ψ t π) (w : (coefficientModel π ℓ).toSubmodule),
          ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0)
    (ℓ : glFunctionals ψ t (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
    (w : (coefficientModel (F.canonicalNormalizedProductInduced (succBlockShape m h) τ)
      ℓ).toSubmodule) :
    ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0 :=
  forall_coefficientModel_of_isGeneric ψ t
    (fun f => ∫ x, whittakerProductIntegrand ψ f H x ∂μ = 0) hH _
    (isGeneric_canonicalNormalizedProductInduced ψ m h τ hirr hsc hprod) ℓ w

/-- The unlinked base case: P4a followed by P4b. -/
theorem integral_whittakerProductIntegrand_eq_zero_of_unlinked
    (ψ : UnitaryAdditiveCharacter F.Carrier) {t k : ℕ} (m : Fin k → ℕ)
    (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hs : ∀ i, IsSmooth (τ i)) (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hunl : ∀ a b, blockDatum τ hs hirr hsc a ≠ (blockDatum τ hs hirr hsc b).twist 1)
    [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
    (μ : Measure (LeftUnipotentQuotient t F.Carrier)) (H : InverseWhittakerFunctions ψ t)
    (hH : ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) V),
      IsGeneric ψ t π →
        ∀ (ℓ : glFunctionals ψ t π) (w : (coefficientModel π ℓ).toSubmodule),
          ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0)
    (ℓ : glFunctionals ψ t (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
    (w : (coefficientModel (F.canonicalNormalizedProductInduced (succBlockShape m h) τ)
      ℓ).toSubmodule) :
    ∫ x, whittakerProductIntegrand ψ w.val H x ∂μ = 0 :=
  integral_whittakerProductIntegrand_canonicalNormalizedProductInduced_eq_zero ψ m h τ hirr
    hsc (isIrreducible_canonicalNormalizedProductInduced_of_unlinked m h τ hs hirr hsc hunl)
    μ H hH ℓ w

end Langlands.Whittaker
