import Langlands.Representation.Unramified.SpectralSystem
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.Adelic

/-! # Arithmetic weak transfer of supplied unramified spectra -/

noncomputable section

open scoped BigOperators NumberField

universe uF uE

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality
open IsDedekindDomain

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [NumberField F] [NumberField E] [Algebra F E]
  {n m : ℕ}

omit [NumberField F] in
/-- A finite set upstairs lies above only finitely many actual base places. -/
theorem eventually_avoidsAbove (U : Finset (FinitePlace E)) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ w : FinitePlacesAbove E v, w.1 ∉ U := by
  classical
  filter_upwards [(U.image (HeightOneSpectrum.under (𝓞 F))).eventually_cofinite_notMem]
    with v hv w
  intro hw
  apply hv
  rw [← finitePlacesAbove_under v w]
  exact Finset.mem_image_of_mem _ hw

/-- The Euler denominator of the numerical induction, expressed without choosing
roots and retaining every actual place and every eigenvalue multiplicity. -/
def inducedEulerPolynomial (t : SpectralSystem (FinitePlace E) m)
    (v : FinitePlace F) (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional) :
    Polynomial ℂ :=
  ∏ w : FinitePlacesAbove E v,
    (t.eulerPolynomial w.1 (ht w)).comp
      (Polynomial.X ^ w.1.asIdeal.inertiaDeg (𝓞 F))

/-- Supplied equal-rank systems satisfy arithmetic weak base change when all
actual places above one cofinite set of base places are unramified, defined,
and related by the actual residue-degree power of the unordered spectrum. -/
def IsArithmeticWeakBaseChangeOf (t : SpectralSystem (FinitePlace E) n)
    (s : SpectralSystem (FinitePlace F) n) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    ∃ (hs : v ∉ s.exceptional)
      (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional),
      (∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1) ∧
      ∀ w : FinitePlacesAbove E v,
        t.eigenvalues w.1 (ht w) =
          (s.eigenvalues v hs).power (w.1.asIdeal.inertiaDeg (𝓞 F))

/-- Arithmetic weak induction for independently supplied ranks. The target rank
is the source rank times the actual field degree, and the Euler identity holds
at every tested base place with both systems defined at every place involved. -/
def IsArithmeticWeakInductionOf (s : SpectralSystem (FinitePlace F) n)
    (t : SpectralSystem (FinitePlace E) m) : Prop :=
  n = m * Module.finrank F E ∧
    ∀ᶠ v in Filter.cofinite,
      ∃ (hs : v ∉ s.exceptional)
        (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional),
        (∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1) ∧
        s.eulerPolynomial v hs = inducedEulerPolynomial t v ht

/-- Proofs of definedness do not affect the induced Euler denominator. -/
theorem inducedEulerPolynomial_congr_defined (t : SpectralSystem (FinitePlace E) m)
    (v : FinitePlace F) (h h' : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional) :
    inducedEulerPolynomial t v h = inducedEulerPolynomial t v h' := rfl

/-- At residue degree one, polynomial substitution is the identity. -/
theorem inducedEulerPolynomial_of_inertiaDeg_eq_one
    (t : SpectralSystem (FinitePlace E) m) (v : FinitePlace F)
    (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional)
    (hf : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.inertiaDeg (𝓞 F) = 1) :
    inducedEulerPolynomial t v ht =
      ∏ w : FinitePlacesAbove E v, t.eulerPolynomial w.1 (ht w) := by
  simp [inducedEulerPolynomial, hf]

/-- Restricting the upstairs system leaves its induced denominator unchanged
where the restricted system is defined. -/
theorem inducedEulerPolynomial_restrict (t : SpectralSystem (FinitePlace E) m)
    (U : Finset (FinitePlace E)) (hU : t.exceptional ⊆ U)
    (v : FinitePlace F) (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ U) :
    inducedEulerPolynomial (t.restrict U hU) v ht =
      inducedEulerPolynomial t v (fun w hw => ht w (hU hw)) := rfl

omit [NumberField F] in
/-- Enlarging the downstairs exceptional set preserves weak base change in both
directions. No value is assigned at any removed place. -/
theorem isArithmeticWeakBaseChangeOf_restrict_down_iff
    (t : SpectralSystem (FinitePlace E) n) (s : SpectralSystem (FinitePlace F) n)
    (U : Finset (FinitePlace F)) (hU : s.exceptional ⊆ U) :
    t.IsArithmeticWeakBaseChangeOf (s.restrict U hU) ↔
      t.IsArithmeticWeakBaseChangeOf s := by
  constructor
  · intro h
    exact h.mono fun v ⟨hs, ht, he, hspec⟩ =>
      ⟨(fun hv => hs (hU hv)), ht, he, hspec⟩
  · intro h
    filter_upwards [h, U.eventually_cofinite_notMem] with v hv hs
    rcases hv with ⟨_, ht, he, hspec⟩
    exact ⟨hs, ht, he, hspec⟩

omit [NumberField F] in
/-- Enlarging the upstairs exceptional set discards its finite image under the
actual contraction map, uniformly over every place above each retained base place. -/
theorem isArithmeticWeakBaseChangeOf_restrict_up_iff
    (t : SpectralSystem (FinitePlace E) n) (s : SpectralSystem (FinitePlace F) n)
    (U : Finset (FinitePlace E)) (hU : t.exceptional ⊆ U) :
    (t.restrict U hU).IsArithmeticWeakBaseChangeOf s ↔
      t.IsArithmeticWeakBaseChangeOf s := by
  constructor
  · intro h
    exact h.mono fun v ⟨hs, ht, he, hspec⟩ =>
      ⟨hs, (fun w hw => ht w (hU hw)), he, hspec⟩
  · intro h
    filter_upwards [h, eventually_avoidsAbove (F := F) U] with v hv ht
    rcases hv with ⟨hs, _, he, hspec⟩
    exact ⟨hs, ht, he, hspec⟩

/-- Weak induction is independent of enlarging the downstairs exceptional set. -/
theorem isArithmeticWeakInductionOf_restrict_down_iff
    (s : SpectralSystem (FinitePlace F) n) (t : SpectralSystem (FinitePlace E) m)
    (U : Finset (FinitePlace F)) (hU : s.exceptional ⊆ U) :
    (s.restrict U hU).IsArithmeticWeakInductionOf t ↔
      s.IsArithmeticWeakInductionOf t := by
  constructor
  · rintro ⟨hrank, h⟩
    exact ⟨hrank, h.mono fun v ⟨hs, ht, he, hp⟩ =>
      ⟨(fun hv => hs (hU hv)), ht, he, hp⟩⟩
  · rintro ⟨hrank, h⟩
    refine ⟨hrank, ?_⟩
    filter_upwards [h, U.eventually_cofinite_notMem] with v hv hs
    rcases hv with ⟨_, ht, he, hp⟩
    exact ⟨hs, ht, he, hp⟩

/-- Weak induction is independent of enlarging the upstairs exceptional set;
the proof removes its actual finite image in the base. -/
theorem isArithmeticWeakInductionOf_restrict_up_iff
    (s : SpectralSystem (FinitePlace F) n) (t : SpectralSystem (FinitePlace E) m)
    (U : Finset (FinitePlace E)) (hU : t.exceptional ⊆ U) :
    s.IsArithmeticWeakInductionOf (t.restrict U hU) ↔
      s.IsArithmeticWeakInductionOf t := by
  constructor
  · rintro ⟨hrank, h⟩
    exact ⟨hrank, h.mono fun v ⟨hs, ht, he, hp⟩ =>
      ⟨hs, (fun w hw => ht w (hU hw)), he, hp⟩⟩
  · rintro ⟨hrank, h⟩
    refine ⟨hrank, ?_⟩
    filter_upwards [h, eventually_avoidsAbove (F := F) U] with v hv ht
    rcases hv with ⟨hs, _, he, hp⟩
    exact ⟨hs, ht, he, hp⟩

omit [NumberField F] in
/-- Residue degree one gives equality of the two supplied unordered spectra. -/
theorem IsArithmeticWeakBaseChangeOf.eigenvalues_of_inertiaDeg_eq_one
    {t : SpectralSystem (FinitePlace E) n} {s : SpectralSystem (FinitePlace F) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) :
    ∀ᶠ v in Filter.cofinite,
      ∃ (hs : v ∉ s.exceptional)
        (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional),
        ∀ w : FinitePlacesAbove E v, w.1.asIdeal.inertiaDeg (𝓞 F) = 1 →
          t.eigenvalues w.1 (ht w) = s.eigenvalues v hs := by
  apply h.mono
  rintro v ⟨hs, ht, _, he⟩
  refine ⟨hs, ht, ?_⟩
  intro w hf
  simpa only [hf, Eigenvalues.power_one] using he w

omit [NumberField F] in
/-- Taking further powers uses the existing multiplication rule for unordered
spectra, uniformly in the further exponent. -/
theorem IsArithmeticWeakBaseChangeOf.powers
    {t : SpectralSystem (FinitePlace E) n} {s : SpectralSystem (FinitePlace F) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) :
    ∀ᶠ v in Filter.cofinite,
      ∃ (hs : v ∉ s.exceptional)
        (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional),
        ∀ (w : FinitePlacesAbove E v) (k : ℕ),
          (t.eigenvalues w.1 (ht w)).power k =
            (s.eigenvalues v hs).power (w.1.asIdeal.inertiaDeg (𝓞 F) * k) := by
  apply h.mono
  rintro v ⟨hs, ht, _, he⟩
  refine ⟨hs, ht, ?_⟩
  intro w k
  rw [he w, Eigenvalues.power_power]

omit [NumberField F] in
/-- Base change compares all power traces with the residue-degree multiplication
of the exponent, with one finite base exception set uniform in the power. -/
theorem IsArithmeticWeakBaseChangeOf.powerTraces
    {t : SpectralSystem (FinitePlace E) n} {s : SpectralSystem (FinitePlace F) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) :
    ∀ᶠ v in Filter.cofinite,
      ∃ (hs : v ∉ s.exceptional)
        (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional),
        ∀ (w : FinitePlacesAbove E v) (k : ℕ),
          t.powerTrace w.1 (ht w) k =
            s.powerTrace v hs (w.1.asIdeal.inertiaDeg (𝓞 F) * k) := by
  apply h.mono
  rintro v ⟨hs, ht, _, he⟩
  refine ⟨hs, ht, ?_⟩
  intro w k
  change (t.eigenvalues w.1 (ht w)).powerTrace k = _
  rw [he w, Eigenvalues.powerTrace_power]
  rfl

end Langlands.Unramified.SpectralSystem
