import Langlands.Automorphic.Unramified.IsobaricArithmeticSpectralTransport
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily
import Langlands.Global.AdelicFunctoriality.FinitePlaceEquivUnder

/-!
# A spectral invariant along towers of base changes

Fix a number field `L` and a multiset-valued profile `X` on the finite places of `L`. Isobaric
data `D` over a subfield `A` of `L` satisfy the invariant when some spectral system `s`
attached to `D` has, at almost every finite place `w` of `L`, the profile value `X w` as the
spectrum of `s` at the place `w ∩ A` raised to the inertia degree of `w` over `A`.

The invariant passes from `A` to `B` along a weak base change for `A ⊆ B ⊆ L`, and along
arithmetic pullbacks compatible with the embeddings into `L`, given the cuspidal transport
statement. It holds for a cuspidal class with the profile of an attached system. Over `L`
itself, it says the spectra of an attached system are the profile values.
-/

noncomputable section

universe u uV uV' uW

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField

namespace Langlands.Unramified

/-- Equal Euler polynomials give equal spectra, read as multisets, even for ranks not known
to be equal in advance. -/
theorem Eigenvalues.coe_eq_of_eulerPolynomial_eq {n m : ℕ} (a : Eigenvalues n)
    (b : Eigenvalues m) (h : a.eulerPolynomial = b.eulerPolynomial) :
    (a : Multiset ℂˣ) = b := by
  have hnm : n = m := by
    rw [← Eigenvalues.eulerPolynomial_natDegree a, h, Eigenvalues.eulerPolynomial_natDegree]
  subst hnm
  rw [Eigenvalues.eulerPolynomial_injective h]

/-- Raising to a power acts on the underlying multiset. -/
theorem Eigenvalues.coe_power {n : ℕ} (a : Eigenvalues n) (k : ℕ) :
    ((a.power k : Eigenvalues n) : Multiset ℂˣ) = (a : Multiset ℂˣ).map (· ^ k) :=
  rfl

/-- The spectrum at a place does not depend on how the place is written. -/
theorem SpectralSystem.eigenvalues_congr {I : Type*} {n : ℕ} (s : SpectralSystem I n)
    {v w : I} (h : v = w) (hv : v ∉ s.exceptional) (hw : w ∉ s.exceptional) :
    s.eigenvalues v hv = s.eigenvalues w hw := by
  subst h
  rfl

end Langlands.Unramified

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

variable {L : Type u} [Field L] [NumberField L]

open Classical in
/-- The profile of a spectral system `s` over a subfield `K` of `L`: at a finite place `w` of
`L`, the spectrum of `s` at `w ∩ K` raised to the inertia degree of `w` over `K`, and the
empty multiset where `s` is not defined at `w ∩ K`. -/
def underPowerProfile {K : Type u} [Field K] [NumberField K] [Algebra K L] {n : ℕ}
    (s : SpectralSystem (Global.FinitePlace K) n) (w : Global.FinitePlace L) : Multiset ℂˣ :=
  if h : w.under (𝓞 K) ∉ s.exceptional then
    ((s.eigenvalues (w.under (𝓞 K)) h : Eigenvalues n) : Multiset ℂˣ).map
      (· ^ w.asIdeal.inertiaDeg (𝓞 K))
  else 0

/-- Isobaric data `D` over a subfield `A` of `L` have total rank `N` and an attached spectral
system whose spectrum at `w ∩ A`, raised to the inertia degree of `w` over `A`, is `X w` for
almost every finite place `w` of `L`. -/
def TowerSpectralInvariant (A : Type u) [Field A] [NumberField A]
    [CompactSpace (AdeleQuotient A)] [Algebra A L] (N : ℕ) (D : IsobaricData A)
    (X : Global.FinitePlace L → Multiset ℂˣ) : Prop :=
  D.rank = N ∧ ∃ s : SpectralSystem (Global.FinitePlace A) D.rank,
    IsobaricData.HasSpectralSystem.{u, uV} D s ∧
      ∀ᶠ w in Filter.cofinite, ∀ hw : w.under (𝓞 A) ∉ s.exceptional,
        ((s.eigenvalues (w.under (𝓞 A)) hw : Eigenvalues D.rank) : Multiset ℂˣ).map
          (· ^ w.asIdeal.inertiaDeg (𝓞 A)) = X w

namespace TowerSpectralInvariant

/-- The invariant passes up along a weak base change for `A ⊆ B ⊆ L`. -/
theorem weakBaseChange {A B : Type u} [Field A] [NumberField A] [Field B] [NumberField B]
    [CompactSpace (AdeleQuotient A)] [CompactSpace (AdeleQuotient B)]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    {N : ℕ} {DA : IsobaricData A} {DB : IsobaricData B} {X : Global.FinitePlace L → Multiset ℂˣ}
    (hA : TowerSpectralInvariant.{u, uV} A N DA X)
    (h : IsobaricData.IsWeakBaseChangeOf.{u, u, uV', uW} DB DA) :
    TowerSpectralInvariant.{u, uW} B N DB X := by
  obtain ⟨hN, sA, hsA, hinv⟩ := hA
  obtain ⟨hr, s, t, hs, ht, hwbc⟩ := h
  refine ⟨hr.trans hN, t, ht, ?_⟩
  have huniq := hsA.eventually_eigenvalues_eq hs
  have htend := WeakInduction.tendsto_under_cofinite (K := A) (L := L)
  filter_upwards [hinv, htend.eventually huniq, htend.eventually hwbc,
    htend.eventually sA.exceptional.eventually_cofinite_notMem] with u hinv huniq hwbc hnot
  intro hu
  obtain ⟨hsv, htw, -, heig⟩ := hwbc
  have hvw : (u.under (𝓞 B)).under (𝓞 A) = u.under (𝓞 A) :=
    HeightOneSpectrum.ext (Ideal.under_under (B := 𝓞 B) u.asIdeal)
  have hlies : (u.under (𝓞 B)).asIdeal.LiesOver (u.under (𝓞 A)).asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal hvw).symm⟩
  have hcoe := congrArg (fun x : Eigenvalues DA.rank => (x : Multiset ℂˣ))
    (heig ⟨u.under (𝓞 B), hlies⟩)
  simp only at hcoe
  rw [SpectralSystem.coe_eigenvalues_eqRec hr t _ _ hu] at hcoe
  have hluB : u.asIdeal.LiesOver (u.under (𝓞 B)).asIdeal := ⟨rfl⟩
  rw [hcoe, ← huniq hnot hsv, ← hinv hnot, Eigenvalues.coe_power, Multiset.map_map,
    Ideal.inertiaDeg_tower (R := 𝓞 A) (u.under (𝓞 B)).asIdeal u.asIdeal]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, pow_mul]

/-- The invariant passes along an arithmetic pullback `e : A ≃+* A'` compatible with the
embeddings into `L`, given the cuspidal transport statement. -/
theorem arithmeticComap (hP : CuspidalArithmeticSpectralTransportStatement.{u, u, uV})
    {A A' : Type u} [Field A] [NumberField A] [Field A'] [NumberField A']
    [CompactSpace (AdeleQuotient A)] [CompactSpace (AdeleQuotient A')]
    [Algebra A L] [Algebra A' L] (e : A ≃+* A')
    (he : ∀ x, algebraMap A' L (e x) = algebraMap A L x) {N : ℕ} {D : IsobaricData A'}
    {X : Global.FinitePlace L → Multiset ℂˣ} (h : TowerSpectralInvariant.{u, uV} A' N D X) :
    TowerSpectralInvariant.{u, uV} A N (D.arithmeticComap e) X := by
  obtain ⟨hN, s, hs, hinv⟩ := h
  obtain ⟨s', hs', heul⟩ := hs.arithmeticComap hP e
  refine ⟨(IsobaricData.rank_arithmeticComap e D).trans hN, s', hs', ?_⟩
  filter_upwards [hinv, (WeakInduction.tendsto_under_cofinite (K := A) (L := L)).eventually heul,
    (WeakInduction.tendsto_under_cofinite (K := A') (L := L)).eventually
      s.exceptional.eventually_cofinite_notMem] with u hinv heul hnot
  intro hu
  have hplace : (finitePlaceEquiv e).symm (u.under (𝓞 A)) = u.under (𝓞 A') := by
    rw [Equiv.symm_apply_eq]
    exact (finitePlaceEquiv_under e he u).symm
  have hw : (finitePlaceEquiv e).symm (u.under (𝓞 A)) ∉ s.exceptional := hplace ▸ hnot
  have hc := Eigenvalues.coe_eq_of_eulerPolynomial_eq _ _ (heul hu hw)
  rw [hc, s.eigenvalues_congr hplace hw hnot, inertiaDeg_eq_of_ringEquiv e he u]
  exact hinv hnot

end TowerSpectralInvariant

omit [NumberField L] in
/-- The one-constituent data of a cuspidal class over `K ⊆ L` satisfy the invariant for the
profile of an attached system. -/
theorem towerSpectralInvariant_ofCuspidal {K : Type u} [Field K] [NumberField K]
    [CompactSpace (AdeleQuotient K)] [Algebra K L] {r : ℕ}
    {c : CuspidalOperatorRealization.IsoClass K r}
    {s : SpectralSystem (Global.FinitePlace K) (r + 1)}
    (hs : CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{u, uV} c s) :
    TowerSpectralInvariant.{u, uV} K (r + 1)
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))
      (underPowerProfile (L := L) s) := by
  refine ⟨rfl, s, IsobaricData.hasSpectralSystem_ofCuspidal_of
    (c := PositiveRankCuspidalClass.ofFixedRank c) hs (SpectralSystem.sameEulerPolynomials_refl _),
    Filter.Eventually.of_forall fun w hw => ?_⟩
  rw [underPowerProfile, dite_eq_left_of_eq_true (eq_true hw)]
  rfl

/-- Over `L` itself the invariant says that the spectra of an attached system are the
profile values at almost every place. -/
theorem TowerSpectralInvariant.eventually_coe_eigenvalues [CompactSpace (AdeleQuotient L)]
    {N : ℕ} {D : IsobaricData L} {X : Global.FinitePlace L → Multiset ℂˣ}
    (h : TowerSpectralInvariant.{u, uV} (L := L) L N D X) :
    D.rank = N ∧ ∃ s : SpectralSystem (Global.FinitePlace L) D.rank,
      IsobaricData.HasSpectralSystem.{u, uV} D s ∧
        ∀ᶠ w in Filter.cofinite, ∀ hw : w ∉ s.exceptional,
          ((s.eigenvalues w hw : Eigenvalues D.rank) : Multiset ℂˣ) = X w := by
  obtain ⟨hN, s, hs, hinv⟩ := h
  refine ⟨hN, s, hs, hinv.mono fun w hw hw' => ?_⟩
  have h1 := inertiaDeg_eq_one_of_finrank_eq_one (K := L) (L := L) (Module.finrank_self L) w
  suffices key : ∀ v : Global.FinitePlace L, v = w → ∀ f : ℕ, f = 1 →
      (∀ hv : v ∉ s.exceptional,
        ((s.eigenvalues v hv : Eigenvalues D.rank) : Multiset ℂˣ).map (· ^ f) = X w) →
      ((s.eigenvalues w hw' : Eigenvalues D.rank) : Multiset ℂˣ) = X w from
    key _ (HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)) _ h1 hw
  rintro v rfl f rfl hv
  simpa using hv hw'

end Langlands.Automorphic.Unramified
