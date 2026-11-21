import Langlands.Automorphic.IsobaricData
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityReduction
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement

/-! # Isolating the Hecke family of a cuspidal class by its constituent count -/

noncomputable section

open scoped BigOperators

universe uF uV uJ uK

set_option autoImplicit false

namespace Langlands.TraceFormula.HeckeIsolation

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Global
open Langlands.Unramified

section Numerical

variable {I : Type*} {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K] {r : K → ℕ}

/-- Reindexing a finite family along an equivalence does not change the Euler
polynomials of its finite sum. -/
theorem sameEulerPolynomials_finiteSum_reindex (e : J ≃ K)
    (u : ∀ k, SpectralSystem I (r k)) :
    (SpectralSystem.finiteSum fun j => u (e j)).SameEulerPolynomials
      (SpectralSystem.finiteSum u) :=
  Filter.Eventually.of_forall fun v hv hv' =>
    (SpectralSystem.finiteSum_eulerPolynomial (fun j => u (e j)) v hv).trans
      ((Fintype.prod_equiv e _ _ fun _ => rfl).trans
        (SpectralSystem.finiteSum_eulerPolynomial u v hv').symm)

end Numerical

section Recovery

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The global recovery statement specializes to each number field. -/
theorem recoveryAt_of_statement
    (h : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    CuspidalEulerConstituentRecoveryAt.{uF, uV} F :=
  h F

/-- The totally complex recovery statement specializes to each totally complex field. -/
theorem recoveryAt_of_TCStatement [NumberField.IsTotallyComplex F]
    (h : CuspidalEulerConstituentRecoveryTCStatement.{uF, uV}) :
    CuspidalEulerConstituentRecoveryAt.{uF, uV} F :=
  h F

/-- A spectral system `s`, of any rank, carries the unramified Hecke family of the
cuspidal class `c₀` when its Euler polynomials agree off a finite set with those of
some system attached to `c₀` through an actual spectral presentation. -/
def CarriesCuspidalHeckeFamily (c₀ : PositiveRankCuspidalClass F) {n : ℕ}
    (s : SpectralSystem (FinitePlace F) n) : Prop :=
  ∃ s₀ : SpectralSystem (FinitePlace F) c₀.rank,
    PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀ ∧ s₀.SameEulerPolynomials s

/-- A system attached to `c₀` carries the Hecke family of `c₀`. -/
theorem carriesCuspidalHeckeFamily_of_hasSpectralSystem {c₀ : PositiveRankCuspidalClass F}
    {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀) :
    CarriesCuspidalHeckeFamily.{uF, uV} c₀ s₀ :=
  ⟨s₀, h₀, SpectralSystem.sameEulerPolynomials_refl s₀⟩

/-- Carrying the Hecke family of `c₀` depends only on Euler polynomials off a finite set. -/
theorem CarriesCuspidalHeckeFamily.of_sameEulerPolynomials
    {c₀ : PositiveRankCuspidalClass F} {n m : ℕ} {s : SpectralSystem (FinitePlace F) n}
    {t : SpectralSystem (FinitePlace F) m} (h : CarriesCuspidalHeckeFamily.{uF, uV} c₀ s)
    (hst : s.SameEulerPolynomials t) : CarriesCuspidalHeckeFamily.{uF, uV} c₀ t := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact ⟨s₀, h₀, h.trans hst⟩

variable (hrec : CuspidalEulerConstituentRecoveryAt.{uF, uV} F)
include hrec

/-- Constituent recovery for families indexed by arbitrary finite types. -/
theorem exists_equiv_of_sameEulerPolynomials {J : Type uJ} {K : Type uK}
    [Fintype J] [Fintype K]
    (c : J → PositiveRankCuspidalClass F) (d : K → PositiveRankCuspidalClass F)
    (s : ∀ j, SpectralSystem (FinitePlace F) (c j).rank)
    (t : ∀ k, SpectralSystem (FinitePlace F) (d k).rank)
    (hs : ∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c j) (s j))
    (ht : ∀ k, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d k) (t k))
    (hst : (SpectralSystem.finiteSum s).SameEulerPolynomials
      (SpectralSystem.finiteSum t)) :
    ∃ e : J ≃ K, ∀ j, c j = d (e j) := by
  classical
  let eJ := (Fintype.equivFin J).symm
  let eK := (Fintype.equivFin K).symm
  obtain ⟨e, he⟩ := hrec _ _ (fun i => c (eJ i)) (fun i => d (eK i))
    (fun i => s (eJ i)) (fun i => t (eK i)) (fun i => hs (eJ i)) (fun i => ht (eK i))
    ((sameEulerPolynomials_finiteSum_reindex eJ s).trans
      (hst.trans (sameEulerPolynomials_finiteSum_reindex eK t).symm))
  refine ⟨eJ.symm.trans (e.trans eK), fun j => ?_⟩
  have h := he (eJ.symm j)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- Two cuspidal classes with attached systems having the same Euler polynomials
off a finite set are equal. -/
theorem eq_of_sameEulerPolynomials {c₀ c₁ : PositiveRankCuspidalClass F}
    {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    {s₁ : SpectralSystem (FinitePlace F) c₁.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀)
    (h₁ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₁ s₁)
    (h : s₀.SameEulerPolynomials s₁) : c₀ = c₁ := by
  obtain ⟨e, he⟩ := exists_equiv_of_sameEulerPolynomials hrec
    (fun _ : Fin 1 => c₀) (fun _ : Fin 1 => c₁) (fun _ => s₀) (fun _ => s₁)
    (fun _ => h₀) (fun _ => h₁)
    ((IsobaricData.sameEulerPolynomials_finiteSum_one (fun _ : Fin 1 => s₀)).symm.trans
      (h.trans (IsobaricData.sameEulerPolynomials_finiteSum_one (fun _ : Fin 1 => s₁))))
  exact he 0

/-- The Hecke family of a cuspidal class is not that of any attached family whose
number of constituents, counted with multiplicity, differs from one. -/
theorem not_sameEulerPolynomials_of_card_ne_one {c₀ : PositiveRankCuspidalClass F}
    {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀)
    {K : Type uK} [Fintype K] (d : K → PositiveRankCuspidalClass F)
    (t : ∀ k, SpectralSystem (FinitePlace F) (d k).rank)
    (ht : ∀ k, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d k) (t k))
    (hK : Fintype.card K ≠ 1) {n : ℕ} (s : SpectralSystem (FinitePlace F) n)
    (hts : (SpectralSystem.finiteSum t).SameEulerPolynomials s) :
    ¬ s₀.SameEulerPolynomials s := by
  intro h
  obtain ⟨e, -⟩ := exists_equiv_of_sameEulerPolynomials hrec
    (fun _ : Fin 1 => c₀) d (fun _ => s₀) t (fun _ => h₀) ht
    ((IsobaricData.sameEulerPolynomials_finiteSum_one (fun _ : Fin 1 => s₀)).symm.trans
      (h.trans hts.symm))
  exact hK ((Fintype.card_congr e).symm.trans (Fintype.card_fin 1))

/-- The block form: a family indexed by `Fin d × Fin m` with at least two blocks
never carries the Hecke family of a single cuspidal class. -/
theorem not_sameEulerPolynomials_of_blocks {c₀ : PositiveRankCuspidalClass F}
    {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀)
    {d m : ℕ} (hd : 1 < d) (c : Fin d × Fin m → PositiveRankCuspidalClass F)
    (t : ∀ a, SpectralSystem (FinitePlace F) (c a).rank)
    (ht : ∀ a, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c a) (t a))
    {n : ℕ} (s : SpectralSystem (FinitePlace F) n)
    (hts : (SpectralSystem.finiteSum t).SameEulerPolynomials s) :
    ¬ s₀.SameEulerPolynomials s := by
  refine not_sameEulerPolynomials_of_card_ne_one hrec h₀ c t ht ?_ s hts
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  intro h
  have h₁ := Nat.eq_one_of_mul_eq_one_right h
  have h₂ := Nat.eq_one_of_mul_eq_one_left h
  omega

/-- The only isobaric constituent datum with an attached system having the Hecke
family of a cuspidal class is the datum of that class. -/
theorem eq_ofCuspidal_of_sameEulerPolynomials {c₀ : PositiveRankCuspidalClass F}
    {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀)
    {D : IsobaricData F} {s : SpectralSystem (FinitePlace F) D.rank}
    (hD : IsobaricData.HasSpectralSystem.{uF, uV} D s)
    (h : s₀.SameEulerPolynomials s) : D = IsobaricData.ofCuspidal c₀ := by
  obtain ⟨k, σ, hσ, t, ht, hts⟩ := hD
  obtain ⟨e, he⟩ := exists_equiv_of_sameEulerPolynomials hrec
    (fun _ : Fin 1 => c₀) σ (fun _ => s₀) t (fun _ => h₀) ht
    ((IsobaricData.sameEulerPolynomials_finiteSum_one (fun _ : Fin 1 => s₀)).symm.trans
      (h.trans hts.symm))
  have hk : k = 1 := by
    have h' := Fintype.card_congr e
    simp only [Fintype.card_fin] at h'
    exact h'.symm
  subst hk
  have h0 : e 0 = 0 := Subsingleton.elim _ _
  have hσ0 : σ 0 = c₀ := (congrArg σ h0.symm).trans (he 0).symm
  rw [← hσ, Finset.univ_unique, Finset.singleton_val, Multiset.map_singleton]
  change ({σ default} : Multiset (PositiveRankCuspidalClass F)) = {c₀}
  rw [Fin.default_eq_zero, hσ0]

/-- Consequently a datum with a number of constituents other than one, such as the
cuspidal support of a residual or properly induced term, cannot carry that Hecke family. -/
theorem not_sameEulerPolynomials_of_isobaric_card_ne_one
    {c₀ : PositiveRankCuspidalClass F} {s₀ : SpectralSystem (FinitePlace F) c₀.rank}
    (h₀ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₀ s₀)
    {D : IsobaricData F} {s : SpectralSystem (FinitePlace F) D.rank}
    (hD : IsobaricData.HasSpectralSystem.{uF, uV} D s) (hcard : Multiset.card D ≠ 1) :
    ¬ s₀.SameEulerPolynomials s := by
  intro h
  apply hcard
  rw [eq_ofCuspidal_of_sameEulerPolynomials hrec h₀ hD h]
  rfl

/-! ### The same statements for `CarriesCuspidalHeckeFamily` -/

/-- A cuspidal class whose attached system carries the Hecke family of `c₀` is `c₀`. -/
theorem eq_of_carriesCuspidalHeckeFamily {c₀ c₁ : PositiveRankCuspidalClass F}
    {s₁ : SpectralSystem (FinitePlace F) c₁.rank}
    (h : CarriesCuspidalHeckeFamily.{uF, uV} c₀ s₁)
    (h₁ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₁ s₁) : c₀ = c₁ := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact eq_of_sameEulerPolynomials hrec h₀ h₁ h

/-- A system with the Euler polynomials of a finite sum attached to a family whose number
of constituents differs from one does not carry the Hecke family of a cuspidal class. -/
theorem not_carriesCuspidalHeckeFamily_of_card_ne_one {c₀ : PositiveRankCuspidalClass F}
    {K : Type uK} [Fintype K] (d : K → PositiveRankCuspidalClass F)
    (t : ∀ k, SpectralSystem (FinitePlace F) (d k).rank)
    (ht : ∀ k, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d k) (t k))
    (hK : Fintype.card K ≠ 1) {n : ℕ} (s : SpectralSystem (FinitePlace F) n)
    (hts : (SpectralSystem.finiteSum t).SameEulerPolynomials s) :
    ¬ CarriesCuspidalHeckeFamily.{uF, uV} c₀ s := by
  rintro ⟨s₀, h₀, h⟩
  exact not_sameEulerPolynomials_of_card_ne_one hrec h₀ d t ht hK s hts h

/-- The block form for `CarriesCuspidalHeckeFamily`. -/
theorem not_carriesCuspidalHeckeFamily_of_blocks {c₀ : PositiveRankCuspidalClass F}
    {d m : ℕ} (hd : 1 < d) (c : Fin d × Fin m → PositiveRankCuspidalClass F)
    (t : ∀ a, SpectralSystem (FinitePlace F) (c a).rank)
    (ht : ∀ a, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c a) (t a))
    {n : ℕ} (s : SpectralSystem (FinitePlace F) n)
    (hts : (SpectralSystem.finiteSum t).SameEulerPolynomials s) :
    ¬ CarriesCuspidalHeckeFamily.{uF, uV} c₀ s := by
  rintro ⟨s₀, h₀, h⟩
  exact not_sameEulerPolynomials_of_blocks hrec h₀ hd c t ht s hts h

/-- An isobaric datum with an attached system carrying the Hecke family of `c₀` is the
datum of `c₀`. -/
theorem eq_ofCuspidal_of_carriesCuspidalHeckeFamily {c₀ : PositiveRankCuspidalClass F}
    {D : IsobaricData F} {s : SpectralSystem (FinitePlace F) D.rank}
    (hD : IsobaricData.HasSpectralSystem.{uF, uV} D s)
    (h : CarriesCuspidalHeckeFamily.{uF, uV} c₀ s) : D = IsobaricData.ofCuspidal c₀ := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact eq_ofCuspidal_of_sameEulerPolynomials hrec h₀ hD h

/-- An isobaric datum with a number of constituents other than one has no attached
system carrying the Hecke family of a cuspidal class. -/
theorem not_carriesCuspidalHeckeFamily_of_isobaric_card_ne_one
    {c₀ : PositiveRankCuspidalClass F} {D : IsobaricData F}
    {s : SpectralSystem (FinitePlace F) D.rank}
    (hD : IsobaricData.HasSpectralSystem.{uF, uV} D s) (hcard : Multiset.card D ≠ 1) :
    ¬ CarriesCuspidalHeckeFamily.{uF, uV} c₀ s := by
  rintro ⟨s₀, h₀, h⟩
  exact not_sameEulerPolynomials_of_isobaric_card_ne_one hrec h₀ hD hcard h

end Recovery

end Langlands.TraceFormula.HeckeIsolation
