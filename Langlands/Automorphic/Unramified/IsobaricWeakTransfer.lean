import Langlands.Automorphic.IsobaricData
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Galois conjugation and weak transfer of isobaric constituent data

The Galois action on isobaric constituent data, constituent by constituent, the Galois
orbit of a cuspidal class as isobaric data, and arithmetic weak base change and weak
induction between isobaric data over a number field and over an extension, through
spectral systems attached to the data. For data of single cuspidal classes the transfer
relations are the published cuspidal class relations.
-/

noncomputable section

open scoped BigOperators

universe uF uE uV uW

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] {n m : ℕ}

omit [NumberField F] in
/-- Agreement of Euler polynomials on a cofinite set of places of `E` holds at all places
above a cofinite set of places of `F`. -/
theorem SameEulerPolynomials.eventually_above {t t' : SpectralSystem (FinitePlace E) m}
    (h : t.SameEulerPolynomials t') :
    ∀ᶠ v : FinitePlace F in Filter.cofinite, ∀ w : FinitePlacesAbove E v,
      w.1 ∉ t'.exceptional ∧ ∀ (h₁ : w.1 ∉ t.exceptional) (h₂ : w.1 ∉ t'.exceptional),
        t.eulerPolynomial w.1 h₁ = t'.eulerPolynomial w.1 h₂ := by
  classical
  obtain hfin := Filter.eventually_cofinite.mp h
  filter_upwards [eventually_avoidsAbove (F := F) (hfin.toFinset ∪ t'.exceptional)]
    with v hv w
  have hw := hv w
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw
  exact ⟨hw.2, hw.1⟩

omit [NumberField F] in
/-- Arithmetic weak base change depends only on Euler polynomials outside finite sets. -/
theorem IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials
    {t t' : SpectralSystem (FinitePlace E) n} {s s' : SpectralSystem (FinitePlace F) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) (hs : s.SameEulerPolynomials s')
    (ht : t.SameEulerPolynomials t') : t'.IsArithmeticWeakBaseChangeOf s' := by
  filter_upwards [h, hs, s'.exceptional.eventually_cofinite_notMem,
    ht.eventually_above (F := F)] with v hv hsv hs' hw
  obtain ⟨hsx, htx, hram, heig⟩ := hv
  refine ⟨hs', fun w => (hw w).1, hram, fun w => ?_⟩
  have e₁ : s.eigenvalues v hsx = s'.eigenvalues v hs' :=
    Eigenvalues.eulerPolynomial_injective (hsv hsx hs')
  have e₂ : t.eigenvalues w.1 (htx w) = t'.eigenvalues w.1 ((hw w).1) :=
    Eigenvalues.eulerPolynomial_injective ((hw w).2 (htx w) ((hw w).1))
  rw [← e₂, heig w, e₁]

/-- The induced Euler polynomial depends only on the Euler polynomials at the places
above. -/
theorem inducedEulerPolynomial_congr {t t' : SpectralSystem (FinitePlace E) m}
    (v : FinitePlace F) (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional)
    (ht' : ∀ w : FinitePlacesAbove E v, w.1 ∉ t'.exceptional)
    (h : ∀ w : FinitePlacesAbove E v, t.eulerPolynomial w.1 (ht w) =
      t'.eulerPolynomial w.1 (ht' w)) :
    inducedEulerPolynomial t v ht = inducedEulerPolynomial t' v ht' := by
  unfold inducedEulerPolynomial
  exact Finset.prod_congr rfl fun w _ => by rw [h w]

/-- Arithmetic weak induction depends only on Euler polynomials outside finite sets. -/
theorem IsArithmeticWeakInductionOf.of_sameEulerPolynomials
    {s s' : SpectralSystem (FinitePlace F) n} {t t' : SpectralSystem (FinitePlace E) m}
    (h : s.IsArithmeticWeakInductionOf t) (hs : s.SameEulerPolynomials s')
    (ht : t.SameEulerPolynomials t') : s'.IsArithmeticWeakInductionOf t' := by
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hs, s'.exceptional.eventually_cofinite_notMem,
    ht.eventually_above (F := F)] with v hv hsv hs' hw
  obtain ⟨hsx, htx, hram, heul⟩ := hv
  refine ⟨hs', fun w => (hw w).1, hram, ?_⟩
  rw [← hsv hsx hs', heul]
  exact inducedEulerPolynomial_congr v htx (fun w => (hw w).1)
    (fun w => (hw w).2 (htx w) ((hw w).1))

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.IsobaricData

open Langlands.Global Langlands.Unramified

section Galois

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField E] [Algebra F E]
  [CompactSpace (AdeleQuotient E)]

/-- The Galois conjugate `D^σ` of isobaric data: every constituent `c` is replaced by its
conjugate `c ∘ σ⁻¹`, with multiplicities. -/
def galoisConj (σ : E ≃ₐ[F] E) (D : IsobaricData E) : IsobaricData E :=
  D.map (PositiveRankCuspidalClass.galoisConj σ)

@[simp] theorem galoisConj_zero (σ : E ≃ₐ[F] E) : galoisConj σ (0 : IsobaricData E) = 0 :=
  Multiset.map_zero _

@[simp] theorem galoisConj_add (σ : E ≃ₐ[F] E) (D D' : IsobaricData E) :
    galoisConj σ (D + D') = galoisConj σ D + galoisConj σ D' :=
  Multiset.map_add _ _ _

@[simp] theorem galoisConj_ofCuspidal (σ : E ≃ₐ[F] E) (c : PositiveRankCuspidalClass E) :
    galoisConj σ (ofCuspidal c) = ofCuspidal (c.galoisConj σ) :=
  Multiset.map_singleton _ _

@[simp] theorem rank_galoisConj (σ : E ≃ₐ[F] E) (D : IsobaricData E) :
    (galoisConj σ D).rank = D.rank := by
  simp only [rank, galoisConj, Multiset.map_map, Function.comp_def,
    PositiveRankCuspidalClass.rank_galoisConj]

@[simp] theorem galoisConj_one (D : IsobaricData E) : galoisConj (1 : E ≃ₐ[F] E) D = D := by
  simp only [galoisConj, PositiveRankCuspidalClass.galoisConj_one, Multiset.map_id']

theorem galoisConj_mul (σ τ : E ≃ₐ[F] E) (D : IsobaricData E) :
    galoisConj (σ * τ) D = galoisConj σ (galoisConj τ D) := by
  simp only [galoisConj, Multiset.map_map, Function.comp_def,
    PositiveRankCuspidalClass.galoisConj_mul]

/-- The Galois action on isobaric data, as an installable action. -/
@[instance_reducible]
def galoisAction : MulAction (E ≃ₐ[F] E) (IsobaricData E) where
  smul := galoisConj
  one_smul := galoisConj_one
  mul_smul := galoisConj_mul

/-- The data are stable under `σ`: `D^σ = D` as multisets. -/
def IsGaloisStable (σ : E ≃ₐ[F] E) (D : IsobaricData E) : Prop :=
  galoisConj σ D = D

variable (F) [FiniteDimensional F E]

/-- The Galois orbit `Π^{τ₁} ⊞ ⋯ ⊞ Π^{τ_ℓ}` of a cuspidal class over `E`, one constituent
for each `τ ∈ Gal(E/F)`. -/
def galoisOrbit (c : PositiveRankCuspidalClass E) : IsobaricData E :=
  (Finset.univ : Finset (E ≃ₐ[F] E)).val.map fun τ => c.galoisConj τ

theorem rank_galoisOrbit (c : PositiveRankCuspidalClass E) :
    (galoisOrbit F c).rank = Fintype.card (E ≃ₐ[F] E) * c.rank := by
  simp only [rank, galoisOrbit, Multiset.map_map, Function.comp_def,
    PositiveRankCuspidalClass.rank_galoisConj, Multiset.map_const', Multiset.sum_replicate,
    Finset.card_val, Finset.card_univ, smul_eq_mul]

theorem rank_galoisOrbit_of_isGalois [IsGalois F E] (c : PositiveRankCuspidalClass E) :
    (galoisOrbit F c).rank = Module.finrank F E * c.rank := by
  rw [rank_galoisOrbit, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-- The Galois orbit is stable under every automorphism. -/
theorem isGaloisStable_galoisOrbit (σ : E ≃ₐ[F] E) (c : PositiveRankCuspidalClass E) :
    IsGaloisStable σ (galoisOrbit F c) := by
  unfold IsGaloisStable galoisConj galoisOrbit
  rw [Multiset.map_map]
  calc (Finset.univ : Finset (E ≃ₐ[F] E)).val.map
        (PositiveRankCuspidalClass.galoisConj σ ∘ fun τ => c.galoisConj τ)
      = (Finset.univ : Finset (E ≃ₐ[F] E)).val.map
          ((fun τ => c.galoisConj τ) ∘ Equiv.mulLeft σ) :=
        Multiset.map_congr rfl fun τ _ =>
          (PositiveRankCuspidalClass.galoisConj_mul σ τ c).symm
    _ = ((Finset.univ : Finset (E ≃ₐ[F] E)).val.map (Equiv.mulLeft σ)).map
          (fun τ => c.galoisConj τ) := (Multiset.map_map _ _ _).symm
    _ = (Finset.univ : Finset (E ≃ₐ[F] E)).val.map (fun τ => c.galoisConj τ) := by
        rw [Multiset.map_univ_val_equiv]

end Galois

section Transfer

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- `DE` is a weak base change of `DF`: the ranks agree, and some spectral system attached to
`DE` is an arithmetic weak base change of some spectral system attached to `DF`. -/
def IsWeakBaseChangeOf (DE : IsobaricData E) (DF : IsobaricData F) : Prop :=
  ∃ (h : DE.rank = DF.rank) (s : SpectralSystem (FinitePlace F) DF.rank)
    (t : SpectralSystem (FinitePlace E) DE.rank),
    HasSpectralSystem.{uF, uV} DF s ∧ HasSpectralSystem.{uE, uW} DE t ∧
      SpectralSystem.IsArithmeticWeakBaseChangeOf (h ▸ t) s

/-- `DF` is weakly induced from `DE`: some spectral system attached to `DF` is the arithmetic
weak induction of some spectral system attached to `DE`. The rank of `DF` is then
`[E : F]` times that of `DE`. -/
def IsWeakInductionOf (DF : IsobaricData F) (DE : IsobaricData E) : Prop :=
  ∃ (s : SpectralSystem (FinitePlace F) DF.rank) (t : SpectralSystem (FinitePlace E) DE.rank),
    HasSpectralSystem.{uF, uV} DF s ∧ HasSpectralSystem.{uE, uW} DE t ∧
      s.IsArithmeticWeakInductionOf t

theorem IsWeakBaseChangeOf.rank_eq {DE : IsobaricData E} {DF : IsobaricData F}
    (h : IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF) : DE.rank = DF.rank :=
  h.1

theorem IsWeakInductionOf.rank_eq {DF : IsobaricData F} {DE : IsobaricData E}
    (h : IsWeakInductionOf.{uF, uE, uV, uW} DF DE) :
    DF.rank = DE.rank * Module.finrank F E := by
  obtain ⟨s, t, _, _, h⟩ := h
  exact h.1

/-- For data of single cuspidal classes, weak base change of data is weak base change of the
classes. -/
theorem isWeakBaseChangeOf_ofCuspidal_iff {r : ℕ}
    (d : CuspidalOperatorRealization.IsoClass E r)
    (c : CuspidalOperatorRealization.IsoClass F r) :
    IsWeakBaseChangeOf.{uF, uE, uV, uW} (ofCuspidal (PositiveRankCuspidalClass.ofFixedRank d))
        (ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)) ↔
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d c := by
  constructor
  · rintro ⟨h, s, t, hs, ht, hst⟩
    obtain ⟨s₀, hs₀, hs₀s⟩ := hs.exists_ofCuspidal
    obtain ⟨t₀, ht₀, ht₀t⟩ := ht.exists_ofCuspidal
    exact ⟨s₀, t₀, hs₀, ht₀,
      SpectralSystem.IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials hst hs₀s.symm
        ht₀t.symm⟩
  · rintro ⟨s, t, hs, ht, hst⟩
    exact ⟨rfl, s, t,
      hasSpectralSystem_ofCuspidal_of (c := PositiveRankCuspidalClass.ofFixedRank c) hs
        (SpectralSystem.sameEulerPolynomials_refl _),
      hasSpectralSystem_ofCuspidal_of (c := PositiveRankCuspidalClass.ofFixedRank d) ht
        (SpectralSystem.sameEulerPolynomials_refl _), hst⟩

/-- For data of single cuspidal classes, weak induction of data is weak induction of the
classes. -/
theorem isWeakInductionOf_ofCuspidal_iff {r q : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r)
    (d : CuspidalOperatorRealization.IsoClass E q) :
    IsWeakInductionOf.{uF, uE, uV, uW} (ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))
        (ofCuspidal (PositiveRankCuspidalClass.ofFixedRank d)) ↔
      CuspidalOperatorRealization.IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c d := by
  constructor
  · rintro ⟨s, t, hs, ht, hst⟩
    obtain ⟨s₀, hs₀, hs₀s⟩ := hs.exists_ofCuspidal
    obtain ⟨t₀, ht₀, ht₀t⟩ := ht.exists_ofCuspidal
    exact ⟨s₀, t₀, hs₀, ht₀,
      SpectralSystem.IsArithmeticWeakInductionOf.of_sameEulerPolynomials hst hs₀s.symm
        ht₀t.symm⟩
  · rintro ⟨s, t, hs, ht, hst⟩
    exact ⟨s, t,
      hasSpectralSystem_ofCuspidal_of (c := PositiveRankCuspidalClass.ofFixedRank c) hs
        (SpectralSystem.sameEulerPolynomials_refl _),
      hasSpectralSystem_ofCuspidal_of (c := PositiveRankCuspidalClass.ofFixedRank d) ht
        (SpectralSystem.sameEulerPolynomials_refl _), hst⟩

end Transfer

end Langlands.Automorphic.IsobaricData
