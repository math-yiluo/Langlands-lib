import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.OperatorUnitaryForm

/-! # Isobaric constituent data

Finite multisets of actual cuspidal classes of positive rank: the constituent data
`Π₁ ⊞ ⋯ ⊞ Π_b` of an isobaric automorphic representation of `GL_n` over a number field,
together with their unitarity condition and the numerical spectral systems attached to them
through actual spectral presentations of the constituents. No isobaric or induced
representation is constructed here; the data are distinguished from any realization.
-/

noncomputable section

open scoped BigOperators

universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Unramified

variable (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Isobaric constituent data over `F`: a finite multiset of actual cuspidal classes of
positive rank, repetitions allowed. -/
abbrev IsobaricData : Type uF :=
  Multiset (PositiveRankCuspidalClass F)

namespace IsobaricData

variable {F}

/-- The rank `n = n₁ + ⋯ + n_b` of the general linear group carrying the isobaric sum. -/
def rank (D : IsobaricData F) : ℕ :=
  (D.map PositiveRankCuspidalClass.rank).sum

theorem rank_eq_sum (D : IsobaricData F) :
    D.rank = (D.map PositiveRankCuspidalClass.rank).sum :=
  rfl

@[simp]
theorem rank_zero : rank (0 : IsobaricData F) = 0 :=
  rfl

@[simp]
theorem rank_add (D D' : IsobaricData F) : (D + D').rank = D.rank + D'.rank := by
  simp [rank]

@[simp]
theorem rank_cons (c : PositiveRankCuspidalClass F) (D : IsobaricData F) :
    rank (c ::ₘ D) = c.rank + D.rank := by
  simp [rank]

@[simp]
theorem rank_singleton (c : PositiveRankCuspidalClass F) :
    rank ({c} : IsobaricData F) = c.rank := by
  simp [rank]

/-- The data of a single cuspidal class. -/
def ofCuspidal (c : PositiveRankCuspidalClass F) : IsobaricData F :=
  {c}

@[simp]
theorem rank_ofCuspidal (c : PositiveRankCuspidalClass F) : (ofCuspidal c).rank = c.rank :=
  rank_singleton c

/-- The data are nonempty exactly when the rank is positive. -/
theorem rank_pos_iff (D : IsobaricData F) : 0 < D.rank ↔ D ≠ 0 := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons c D _ =>
    rw [← Multiset.singleton_add, rank_add, rank_singleton]
    simp [c.rank_pos]

/-- Every constituent is unitarizable: the cuspidal data of Arthur–Clozel's representations
induced from cuspidal, Definition III.4.1, are unitary. -/
def IsUnitary (D : IsobaricData F) : Prop :=
  ∀ c ∈ D, c.2.toOperatorClass.IsUnitarizable

@[simp]
theorem isUnitary_zero : IsUnitary (0 : IsobaricData F) := by
  simp [IsUnitary]

@[simp]
theorem isUnitary_add {D D' : IsobaricData F} :
    (D + D').IsUnitary ↔ D.IsUnitary ∧ D'.IsUnitary := by
  simp only [IsUnitary, Multiset.mem_add]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

@[simp]
theorem isUnitary_ofCuspidal {c : PositiveRankCuspidalClass F} :
    (ofCuspidal c).IsUnitary ↔ c.2.toOperatorClass.IsUnitarizable := by
  simp [IsUnitary, ofCuspidal]

/-- The spectral system `s` of rank `D.rank` is attached to the isobaric data `D`: for some
enumeration `σ : Fin k → PositiveRankCuspidalClass F` of the constituents with their
multiplicities, and some spectral systems `t j` attached to the classes `σ j` through actual
spectral presentations, the Euler polynomials of `s` agree outside a finite set with the
products of the Euler polynomials of the `t j`. -/
def HasSpectralSystem (D : IsobaricData F) (s : SpectralSystem (FinitePlace F) D.rank) :
    Prop :=
  ∃ (k : ℕ) (σ : Fin k → PositiveRankCuspidalClass F) (_ : Finset.univ.val.map σ = D)
    (t : ∀ j, SpectralSystem (FinitePlace F) (σ j).rank),
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (σ j) (t j)) ∧
      (SpectralSystem.finiteSum t).SameEulerPolynomials s

/-- Attachment depends only on Euler polynomials outside a finite set. -/
theorem HasSpectralSystem.of_sameEulerPolynomials {D : IsobaricData F}
    {s s' : SpectralSystem (FinitePlace F) D.rank} (hs : HasSpectralSystem.{uF, uV} D s)
    (hss' : s.SameEulerPolynomials s') : HasSpectralSystem.{uF, uV} D s' := by
  obtain ⟨k, σ, hσ, t, ht, hts⟩ := hs
  exact ⟨k, σ, hσ, t, ht, hts.trans hss'⟩

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
/-- A one-term finite sum has the Euler polynomials of its term. -/
theorem sameEulerPolynomials_finiteSum_one {r : Fin 1 → ℕ}
    (t : ∀ j, SpectralSystem (FinitePlace F) (r j)) :
    (t 0).SameEulerPolynomials (SpectralSystem.finiteSum t) :=
  Filter.Eventually.of_forall fun v _ ht => by
    have h := SpectralSystem.finiteSum_eulerPolynomial t v ht
    rw [Fin.prod_univ_one] at h
    exact h.symm

/-- A spectral system attached to a cuspidal class is, up to Euler polynomials outside a finite
set, attached to the data of that class. -/
theorem hasSpectralSystem_ofCuspidal_of {c : PositiveRankCuspidalClass F}
    {t : SpectralSystem (FinitePlace F) c.rank}
    (ht : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c t)
    {s : SpectralSystem (FinitePlace F) (ofCuspidal c).rank}
    (hts : t.SameEulerPolynomials s) : HasSpectralSystem.{uF, uV} (ofCuspidal c) s :=
  ⟨1, fun _ => c, by simp [ofCuspidal], fun _ => t, fun _ => ht,
    (sameEulerPolynomials_finiteSum_one (fun _ : Fin 1 => t)).symm.trans hts⟩

/-- Conversely, data of one cuspidal class have attached systems only through systems
attached to that class. -/
theorem HasSpectralSystem.exists_ofCuspidal {c : PositiveRankCuspidalClass F}
    {s : SpectralSystem (FinitePlace F) (ofCuspidal c).rank}
    (hs : HasSpectralSystem.{uF, uV} (ofCuspidal c) s) :
    ∃ t : SpectralSystem (FinitePlace F) c.rank,
      PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c t ∧ t.SameEulerPolynomials s := by
  obtain ⟨k, σ, hσD, t, ht, hts⟩ := hs
  have hk : k = 1 := by
    simpa [ofCuspidal] using congrArg Multiset.card hσD
  subst hk
  have hσ : σ 0 = c := by
    have hmem : σ 0 ∈ (ofCuspidal c : IsobaricData F) :=
      hσD ▸ Multiset.mem_map_of_mem σ (Finset.mem_univ_val 0)
    simpa [ofCuspidal] using hmem
  have aux : ∀ (c' : PositiveRankCuspidalClass F), c' = c →
      ∀ t' : SpectralSystem (FinitePlace F) c'.rank,
        PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c' t' →
          t'.SameEulerPolynomials s →
            ∃ t'' : SpectralSystem (FinitePlace F) c.rank,
              PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c t'' ∧
                t''.SameEulerPolynomials s := by
    rintro c' rfl t' h₁ h₂
    exact ⟨t', h₁, h₂⟩
  exact aux (σ 0) hσ (t 0) (ht 0) ((sameEulerPolynomials_finiteSum_one t).trans hts)

end IsobaricData

end Langlands.Automorphic
