import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingBase
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.Representation.Induction.CompactFunctionalPairing
import Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof

/-!
# Unequal-rank compact pairings and inverse-standard Whittaker functionals

For `n < r`, the unequal-rank covariant forms on the compact mirabolic model of rank
`r + 1` against a smooth representation `η` of `GL_(n+1)` embed linearly into the
inverse-standard Whittaker functionals of `η`, and there is a nonzero form as soon as `η`
has a nonzero such functional. The proof reduces `r` to `n + 1` by restriction along the
successor embedding and identifies the adjacent-rank forms with invariant forms on
`c-Ind_N^(GL_(n+1)) θ × η`. Consequently the form space is a line whenever the
inverse-standard Whittaker functionals of `η` form a line.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Topology
open scoped ENNReal

universe uF uW

namespace UnequalRankCompactPairing

/-- A nonzero vector of which every vector is a multiple spans a line. -/
theorem exists_injective_of_forall_eq_smul {X : Type*} [AddCommGroup X] [Module ℂ X] {x : X}
    (hx : x ≠ 0) (h : ∀ y : X, ∃ c : ℂ, y = c • x) :
    ∃ E : X →ₗ[ℂ] ℂ, Function.Injective E := by
  have hS : ∀ y : X, y ∈ ℂ ∙ x := fun y => by
    obtain ⟨c, rfl⟩ := h y
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
  refine ⟨(LinearEquiv.toSpanNonzeroSingleton ℂ X x hx).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (ℂ ∙ x) LinearMap.id hS, ?_⟩
  intro y z hyz
  have h' := (LinearEquiv.toSpanNonzeroSingleton ℂ X x hx).symm.injective hyz
  exact congrArg Subtype.val h'

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {n : ℕ} (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

omit [IsTopologicalDivisionRing F] [T2Space F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)] in
/-- The inverse standard character is the pointwise inverse of the standard character. -/
theorem inverseStandardCharacter_mul (h : GeneralLinear.upperUnipotent (n + 1) F) :
    (inverseStandardCharacter ψ n h : ℂ) * standardCharacter ψ n h = 1 := by
  change ((standardCharacter ψ n h : ℂ)⁻¹) * (standardCharacter ψ n h : ℂ) = 1
  exact inv_mul_cancel₀ (Units.ne_zero _)

variable [MeasurableSpace (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]
  [BorelSpace (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]
  (ν : Measure (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)))

/-- Adjacent-rank forms embed into the inverse-standard Whittaker functionals. -/
theorem exists_injective_adjacent (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv)
    (hker : IsOpen ((standardCharacter ψ n).ker : Set (GeneralLinear.upperUnipotent (n + 1) F)))
    (hinv : ∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) →
        0 < ν (QuotientIntegration.compactOpenQuotientOrbit _ J) ∧
          ν (QuotientIntegration.compactOpenQuotientOrbit _ J) < ⊤)
    (hη : IsSmooth η) (s : ℂ) :
    ∃ L : unequalRankMirabolicForms (Nat.lt_add_one n) ψ abv
        (mirabolicCompactInduced ψ (n + 1)) η s →ₗ[ℂ]
        Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
          (inverseStandardCharacter ψ n) η,
      Function.Injective L := by
  have hG : ∀ O : Set (Langlands.GeneralLinear (n + 1) F), IsOpen O →
      (1 : Langlands.GeneralLinear (n + 1) F) ∈ O →
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)) ∧
          (K : Set (Langlands.GeneralLinear (n + 1) F)) ⊆ O :=
    fun O hO h1 => compactOpenSubgroupBasis _ O (hO.mem_nhds h1)
  have hσ := MirabolicCompactTwistedPairing.isSmooth_characterRepresentation _ hker
  have hL := Induction.FormsFunctional.exists_injective_formsFunctional hG
    (GeneralLinear.upperUnipotent (n + 1) F) GeneralLinear.UpperUnipotent.isClosed
    (standardCharacter ψ n) hσ η hη ν hinv hmass (inverseStandardCharacter ψ n)
    (inverseStandardCharacter_mul ψ)
  let e := formsAdjacentEquiv ψ abv η hψ hopen s
  exact ⟨hL.choose ∘ₗ e.toLinearMap, fun x y h => e.injective (hL.choose_spec h)⟩

/-- Adjacent-rank forms are nonzero when `η` has a nonzero inverse-standard Whittaker
functional. -/
theorem exists_ne_zero_adjacent [IsFiniteMeasureOnCompacts ν]
    (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv)
    (hker : IsOpen ((standardCharacter ψ n).ker : Set (GeneralLinear.upperUnipotent (n + 1) F)))
    (hinv : ∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) →
        0 < ν (QuotientIntegration.compactOpenQuotientOrbit _ J) ∧
          ν (QuotientIntegration.compactOpenQuotientOrbit _ J) < ⊤)
    (hη : IsSmooth η)
    (hWh : Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (n + 1) F)
      (θ := inverseStandardCharacter ψ n) η) (s : ℂ) :
    ∃ B : unequalRankMirabolicForms (Nat.lt_add_one n) ψ abv
        (mirabolicCompactInduced ψ (n + 1)) η s, B ≠ 0 := by
  have hG : ∀ O : Set (Langlands.GeneralLinear (n + 1) F), IsOpen O →
      (1 : Langlands.GeneralLinear (n + 1) F) ∈ O →
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)) ∧
          (K : Set (Langlands.GeneralLinear (n + 1) F)) ⊆ O :=
    fun O hO h1 => compactOpenSubgroupBasis _ O (hO.mem_nhds h1)
  have hσ := MirabolicCompactTwistedPairing.isSmooth_characterRepresentation _ hker
  have hB := Induction.CompactFunctionalPairing.exists_nonzero_form _ _ _ η hη hWh.choose
    (inverseStandardCharacter_mul ψ) ν hG hσ hinv hmass hWh.choose_spec
  let e := formsAdjacentEquiv ψ abv η hψ hopen s
  exact ⟨e.symm ⟨hB.choose, hB.choose_spec.1⟩, fun h0 => hB.choose_spec.2
    (congrArg Subtype.val (e.symm.injective (h0.trans (map_zero e.symm).symm)))⟩

/-- For every `n < r`, the forms embed into the inverse-standard Whittaker functionals. -/
theorem exists_injective (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv)
    (hker : IsOpen ((standardCharacter ψ n).ker : Set (GeneralLinear.upperUnipotent (n + 1) F)))
    (hinv : ∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) →
        0 < ν (QuotientIntegration.compactOpenQuotientOrbit _ J) ∧
          ν (QuotientIntegration.compactOpenQuotientOrbit _ J) < ⊤)
    (hη : IsSmooth η) {r : ℕ} (hnr : n < r) (s : ℂ) :
    ∃ L : unequalRankMirabolicForms hnr ψ abv (mirabolicCompactInduced ψ r) η s →ₗ[ℂ]
        Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
          (inverseStandardCharacter ψ n) η,
      Function.Injective L := by
  refine Nat.le_induction (m := n + 1) (P := fun r hr => ∀ s : ℂ,
      ∃ L : unequalRankMirabolicForms hr ψ abv (mirabolicCompactInduced ψ r) η s →ₗ[ℂ]
        Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
          (inverseStandardCharacter ψ n) η, Function.Injective L) ?_ ?_ r hnr s
  · intro s
    exact exists_injective_adjacent ψ abv η ν hψ hopen hker hinv hmass hη s
  · intro m hm ih s
    have hL := ih (s - 1 / 2)
    let e := formsSuccEquiv ψ abv η hm hψ s
    exact ⟨hL.choose ∘ₗ e.symm.toLinearMap, fun x y h => e.symm.injective (hL.choose_spec h)⟩

/-- For every `n < r`, there is a nonzero form when `η` has a nonzero inverse-standard
Whittaker functional. -/
theorem exists_ne_zero [IsFiniteMeasureOnCompacts ν]
    (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv)
    (hker : IsOpen ((standardCharacter ψ n).ker : Set (GeneralLinear.upperUnipotent (n + 1) F)))
    (hinv : ∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) →
        0 < ν (QuotientIntegration.compactOpenQuotientOrbit _ J) ∧
          ν (QuotientIntegration.compactOpenQuotientOrbit _ J) < ⊤)
    (hη : IsSmooth η)
    (hWh : Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (n + 1) F)
      (θ := inverseStandardCharacter ψ n) η) {r : ℕ} (hnr : n < r) (s : ℂ) :
    ∃ B : unequalRankMirabolicForms hnr ψ abv (mirabolicCompactInduced ψ r) η s, B ≠ 0 := by
  refine Nat.le_induction (m := n + 1) (P := fun r hr => ∀ s : ℂ,
      ∃ B : unequalRankMirabolicForms hr ψ abv (mirabolicCompactInduced ψ r) η s, B ≠ 0)
    ?_ ?_ r hnr s
  · intro s
    exact exists_ne_zero_adjacent ψ abv η ν hψ hopen hker hinv hmass hη hWh s
  · intro m hm ih s
    have hB := ih (s - 1 / 2)
    let e := formsSuccEquiv ψ abv η hm hψ s
    exact ⟨e hB.choose, fun h0 => hB.choose_spec (e.injective (h0.trans (map_zero e).symm))⟩

/-- If the inverse-standard Whittaker functionals of `η` form a line, then so do the
unequal-rank forms, for every `n < r` and every `s`. -/
theorem nonempty_equiv_complex [IsFiniteMeasureOnCompacts ν]
    (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv)
    (hker : IsOpen ((standardCharacter ψ n).ker : Set (GeneralLinear.upperUnipotent (n + 1) F)))
    (hinv : ∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) →
        0 < ν (QuotientIntegration.compactOpenQuotientOrbit _ J) ∧
          ν (QuotientIntegration.compactOpenQuotientOrbit _ J) < ⊤)
    (hη : IsSmooth η)
    (hWh : Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (n + 1) F)
      (θ := inverseStandardCharacter ψ n) η)
    (hline : ∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁)
    {r : ℕ} (hnr : n < r) (s : ℂ) :
    Nonempty (unequalRankMirabolicForms hnr ψ abv (mirabolicCompactInduced ψ r) η s ≃ₗ[ℂ] ℂ) := by
  have hL := exists_injective ψ abv η ν hψ hopen hker hinv hmass hη hnr s
  have hB := exists_ne_zero ψ abv η ν hψ hopen hker hinv hmass hη hWh hnr s
  have hx : hWh.choose ≠ 0 := fun h => hWh.choose_spec (congrArg Subtype.val h)
  have hE := exists_injective_of_forall_eq_smul hx (hline hWh.choose · hWh.choose_spec)
  exact MirabolicCompactTwistedPairing.nonempty_linearEquiv_complex (hE.choose ∘ₗ hL.choose)
    (fun x y h => hL.choose_spec (hE.choose_spec h)) hB.choose_spec

end Generic

/-- For a p-adic field with its supplied topology, the unequal-rank forms on the actual
compact mirabolic model against a smooth representation `η` with a nonzero
inverse-standard Whittaker functional form a line, provided the inverse-standard
Whittaker functionals of `η` form a line. -/
theorem nonempty_equiv_complex_padic {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n r : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W,
      IsSmooth η →
      Whittaker.HasFunctional
        (N := GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (θ := Whittaker.inverseStandardCharacter ψ n) η →
      (∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁) →
      ∀ s : ℂ,
        Nonempty
          ((unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
            (Whittaker.mirabolicCompactInduced ψ r) η s) ≃ₗ[ℂ] ℂ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := MirabolicCompactTwistedPairing.valuative_nonarchimedean (K := F.Carrier)
  have : ∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearNonarchimedean
  have : ∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearLocallyCompactSpace
  intro hnr ψ W _ _ η hη hWh hline s
  have hker : IsOpen ((standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) := by
    have := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear.upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
      (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
      (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) := ⟨rfl⟩
  have hν := unipotentQuotientHaar_isCompatible F.Carrier n
  have : IsFiniteMeasureOnCompacts (unipotentQuotientHaar F.Carrier n) := inferInstance
  exact nonempty_equiv_complex ψ (normalizedAbsoluteValue T) η (unipotentQuotientHaar F.Carrier n)
    (MirabolicWhittaker.isOpen_complex_eq_one ψ)
    (MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue T) hker
    hν.right_invariant hν.compactOpenQuotientOrbit_mass hη hWh hline hnr s

end UnequalRankCompactPairing

end Langlands.RankinSelberg
