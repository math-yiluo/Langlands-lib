import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-!
# Constituent recovery from Jacquet–Shalika trace independence

The three conjuncts of `CuspidalSpectralRigidityStatement` reduce to the first one:

* `CuspidalPowerTraceIndependenceStatement` (Jacquet–Shalika 1981, II, Theorem 4.2)
  implies `CuspidalPowerTraceConstituentRecoveryStatement` (the numerical step of
  Theorem 4.4): collect the distinct classes of both lists; the premise becomes a vanishing
  relation whose coefficients are differences of multiplicities, and independence makes
  them zero;
* `CuspidalPowerTraceConstituentRecoveryStatement` implies
  `CuspidalEulerConstituentRecoveryStatement`: the Euler polynomial of a spectrum determines
  the spectrum with multiplicities, hence all its power traces.

Two systems attached to the same class have the same spectra outside both exceptional sets:
both are spectral systems of presentations of one realization
(`CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff`), compared by
`CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`.

Both reductions work over one number field at a time. They are proved for the fieldwise
bodies `CuspidalPowerTraceIndependenceAt F`, `CuspidalPowerTraceConstituentRecoveryAt F` and
`CuspidalEulerConstituentRecoveryAt F` of the three statements, and the statements over all
fields follow.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe uF uV

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified

/-- The body of `CuspidalPowerTraceIndependenceStatement` over one number field `F`. -/
def CuspidalPowerTraceIndependenceAt (F : Type uF) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (p : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    Function.Injective c →
    ∀ (S : Finset (FinitePlace F)) (hS : ∀ i, (s i).exceptional ⊆ S)
      (a : Fin p → ℂ),
      (∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
        (∑ i, a i * (s i).powerTrace v (fun h => hv (hS i h)) k) = 0) →
      ∀ i, a i = 0

/-- The body of `CuspidalPowerTraceConstituentRecoveryStatement` over one number field `F`. -/
def CuspidalPowerTraceConstituentRecoveryAt (F : Type uF) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SamePowerTraces (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

/-- The body of `CuspidalEulerConstituentRecoveryStatement` over one number field `F`. -/
def CuspidalEulerConstituentRecoveryAt (F : Type uF) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

namespace CuspidalSpectralRigidityReduction

/-! ### Euler polynomials determine power traces -/

/-- Equal Euler polynomials have equal underlying multisets of eigenvalues, even for
spectra of possibly different ranks. -/
theorem coe_eq_of_eulerPolynomial_eq {n m : ℕ} (x : Langlands.Unramified.Eigenvalues n)
    (y : Langlands.Unramified.Eigenvalues m) (h : x.eulerPolynomial = y.eulerPolynomial) :
    (x : Multiset ℂˣ) = (y : Multiset ℂˣ) := by
  have hr := congrArg Polynomial.roots h
  rw [Langlands.Unramified.Eigenvalues.eulerPolynomial_roots,
    Langlands.Unramified.Eigenvalues.eulerPolynomial_roots] at hr
  have hinj : Function.Injective fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) :=
    fun a b hab => inv_injective (Units.ext hab)
  exact Multiset.map_injective hinj hr

/-- Equal Euler polynomials have equal power traces. -/
theorem powerTrace_eq_of_eulerPolynomial_eq {n m : ℕ} (x : Langlands.Unramified.Eigenvalues n)
    (y : Langlands.Unramified.Eigenvalues m) (h : x.eulerPolynomial = y.eulerPolynomial)
    (k : ℕ) : x.powerTrace k = y.powerTrace k := by
  unfold Langlands.Unramified.Eigenvalues.powerTrace
  rw [coe_eq_of_eulerPolynomial_eq x y h]

/-- Systems with the same Euler polynomials outside a finite set have the same power traces
outside a finite set. -/
theorem SameEulerPolynomials.samePowerTraces {I : Type*} {n m : ℕ} {s : SpectralSystem I n}
    {t : SpectralSystem I m} (h : s.SameEulerPolynomials t) : s.SamePowerTraces t :=
  h.mono fun _ hv hs ht k _ => powerTrace_eq_of_eulerPolynomial_eq _ _ (hv hs ht) k

/-! ### Two systems attached to one class -/

/-- Two systems attached to equal classes have the same power traces outside both
exceptional sets. -/
theorem powerTrace_eq_of_hasSpectralSystem {F : Type uF} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {c₁ c₂ : PositiveRankCuspidalClass F} (hc : c₁ = c₂)
    {σ : SpectralSystem (FinitePlace F) c₁.rank} {τ : SpectralSystem (FinitePlace F) c₂.rank}
    (hσ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₁ σ)
    (hτ : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c₂ τ)
    (v : FinitePlace F) (hv : v ∉ σ.exceptional) (hv' : v ∉ τ.exceptional) (k : ℕ) :
    σ.powerTrace v hv k = τ.powerTrace v hv' k := by
  subst hc
  obtain ⟨S, P, hS, rfl⟩ := hσ
  have hτ' : CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uV} S.isoClass τ := by
    rw [hS]
    exact hτ
  obtain ⟨Q, rfl⟩ := (CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff S τ).mp hτ'
  unfold SpectralSystem.powerTrace
  rw [CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq P Q v hv hv']

/-! ### Matching fibres -/

/-- Two maps of finite types into a type with decidable equality whose fibres have the same
cardinalities differ by an equivalence of the domains. -/
theorem exists_equiv_of_card_fiber_eq {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] (φ : α → γ) (ψ : β → γ)
    (h : ∀ y, Fintype.card {a // φ a = y} = Fintype.card {b // ψ b = y}) :
    ∃ e : α ≃ β, ∀ a, ψ (e a) = φ a := by
  let E : (Σ y, {a // φ a = y}) ≃ (Σ y, {b // ψ b = y}) :=
    Equiv.sigmaCongrRight fun y => Fintype.equivOfCardEq (h y)
  refine ⟨(Equiv.sigmaFiberEquiv φ).symm.trans (E.trans (Equiv.sigmaFiberEquiv ψ)), fun a => ?_⟩
  exact (E ((Equiv.sigmaFiberEquiv φ).symm a)).2.2

/-- A sum of `1` over the indices of one list and `-1` over those of another, restricted to
a fibre, is the difference of the fibre cardinalities. -/
theorem sum_sign_fiber {p q : ℕ} (ρ : Fin p ⊕ Fin q → Fin p ⊕ Fin q) (y : Fin p ⊕ Fin q) :
    (∑ x, if ρ x = y then (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) x) else 0) =
      (Fintype.card {i // ρ (Sum.inl i) = y} : ℂ) - Fintype.card {j // ρ (Sum.inr j) = y} := by
  classical
  rw [Fintype.sum_sum_type, Fintype.card_subtype, Fintype.card_subtype]
  have h1 : (∑ i : Fin p, if ρ (Sum.inl i) = y then
      (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (Sum.inl i : Fin p ⊕ Fin q)) else 0) =
      ((Finset.univ.filter fun i => ρ (Sum.inl i) = y).card : ℂ) := by
    rw [← Finset.sum_boole]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl
  have h2 : (∑ j : Fin q, if ρ (Sum.inr j) = y then
      (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (Sum.inr j : Fin p ⊕ Fin q)) else 0) =
      -((Finset.univ.filter fun j => ρ (Sum.inr j) = y).card : ℂ) := by
    rw [← Finset.sum_boole, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [h1, h2, sub_eq_add_neg]

end CuspidalSpectralRigidityReduction

open CuspidalSpectralRigidityReduction

/-- **Constituent recovery from trace independence, over one field.** Jacquet–Shalika
(1981), II, the numerical step of Theorem 4.4, from Theorem 4.2. -/
theorem cuspidalPowerTraceConstituentRecoveryAt_of_independenceAt {F : Type uF} [Field F]
    [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hind : CuspidalPowerTraceIndependenceAt.{uF, uV} F) :
    CuspidalPowerTraceConstituentRecoveryAt.{uF, uV} F := by
  classical
  intro p q c d s t hs ht hST
  rcases isEmpty_or_nonempty (Fin p ⊕ Fin q) with hE | hne
  · have : IsEmpty (Fin p) := ⟨fun i => hE.false (Sum.inl i)⟩
    have : IsEmpty (Fin q) := ⟨fun j => hE.false (Sum.inr j)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _, fun i => isEmptyElim i⟩
  -- the combined family
  let g : Fin p ⊕ Fin q → PositiveRankCuspidalClass F := Sum.elim c d
  let u : ∀ x, SpectralSystem (FinitePlace F) (g x).rank := fun x =>
    match x with
    | Sum.inl i => s i
    | Sum.inr j => t j
  have hu : ∀ x, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (g x) (u x) := by
    rintro (i | j)
    · exact hs i
    · exact ht j
  -- a representative index of each class
  let rep : Fin p ⊕ Fin q → Fin p ⊕ Fin q := fun x => Function.invFun g (g x)
  have hgrep : ∀ x, g (rep x) = g x := fun x => Function.invFun_eq ⟨x, rfl⟩
  have hrep_iff : ∀ x y, rep x = rep y ↔ g x = g y := fun x y =>
    ⟨fun h => by rw [← hgrep x, h, hgrep y], fun h => by simp only [rep, h]⟩
  let R : Finset (Fin p ⊕ Fin q) := Finset.univ.image rep
  let eR : Fin R.card ≃ R := R.equivFin.symm
  let c' : Fin R.card → PositiveRankCuspidalClass F := fun b => g (eR b).val
  let s' : ∀ b, SpectralSystem (FinitePlace F) (c' b).rank := fun b => u (eR b).val
  have hc' : ∀ b, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c' b) (s' b) :=
    fun b => hu _
  have hinj : Function.Injective c' := by
    intro a b hab
    apply eR.injective
    apply Subtype.ext
    obtain ⟨xa, -, hxa⟩ := Finset.mem_image.mp (eR a).2
    obtain ⟨xb, -, hxb⟩ := Finset.mem_image.mp (eR b).2
    rw [← hxa, ← hxb]
    apply (hrep_iff xa xb).mpr
    have hab' : g (eR a).val = g (eR b).val := hab
    rw [← hxa, ← hxb, hgrep, hgrep] at hab'
    exact hab'
  -- coefficients: differences of multiplicities
  let ε : Fin p ⊕ Fin q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
  let a : Fin R.card → ℂ := fun b => ∑ x, if rep x = (eR b).val then ε x else 0
  -- the finite set outside which the trace premise holds
  have hcof := (SpectralSystem.finiteSum_samePowerTraces_iff s t).mp hST
  obtain hfin := Filter.eventually_cofinite.mp hcof
  let S : Finset (FinitePlace F) :=
    hfin.toFinset ∪ Finset.univ.biUnion fun x => (u x).exceptional
  have hexc : ∀ x, (u x).exceptional ⊆ S := fun x v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hv⟩)
  have hS' : ∀ b, (s' b).exceptional ⊆ S := fun b => hexc _
  have hrel : ∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
      (∑ b, a b * (s' b).powerTrace v (fun h => hv (hS' b h)) k) = 0 := by
    intro v hv k hk
    have hvu : ∀ x, v ∉ (u x).exceptional := fun x h => hv (hexc x h)
    -- the trace premise at `v`
    have hvB : v ∉ hfin.toFinset := fun h => hv (Finset.mem_union_left _ h)
    have hP : ∀ (hs₀ : v ∉ SpectralSystem.familyExceptional s)
        (ht₀ : v ∉ SpectralSystem.familyExceptional t), ∀ k : ℕ, 0 < k →
        (∑ i, (s i).powerTrace v (SpectralSystem.not_mem_exceptional s v hs₀ i) k) =
          ∑ j, (t j).powerTrace v (SpectralSystem.not_mem_exceptional t v ht₀ j) k := by
      by_contra hcon
      exact hvB (hfin.mem_toFinset.mpr hcon)
    have hs₀ : v ∉ SpectralSystem.familyExceptional s := by
      intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      exact hvu (Sum.inl i) hi
    have ht₀ : v ∉ SpectralSystem.familyExceptional t := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp h
      exact hvu (Sum.inr j) hj
    have hP' := hP hs₀ ht₀ k hk
    -- trace of a combined index, read at its representative
    let τ : Fin p ⊕ Fin q → ℂ := fun x => (u x).powerTrace v (hvu x) k
    have hτrep : ∀ x, τ (rep x) = τ x := fun x =>
      powerTrace_eq_of_hasSpectralSystem (hgrep x) (hu (rep x)) (hu x) v _ _ k
    have hsum0 : (∑ x, ε x * τ x) = 0 := by
      rw [Fintype.sum_sum_type]
      have h1 : (∑ i : Fin p, ε (Sum.inl i) * τ (Sum.inl i)) =
          ∑ i, (s i).powerTrace v (SpectralSystem.not_mem_exceptional s v hs₀ i) k :=
        Finset.sum_congr rfl fun i _ => one_mul _
      have h2 : (∑ j : Fin q, ε (Sum.inr j) * τ (Sum.inr j)) =
          -∑ j, (t j).powerTrace v (SpectralSystem.not_mem_exceptional t v ht₀ j) k := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => neg_one_mul _
      rw [h1, h2, hP', add_neg_cancel]
    -- regroup by representatives
    have hgroup : (∑ x, ε x * τ x) = ∑ y ∈ R, (∑ x, if rep x = y then ε x else 0) * τ y := by
      have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin p ⊕ Fin q)), rep x ∈ R :=
        fun x _ => Finset.mem_image_of_mem rep (Finset.mem_univ x)
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxy : rep x = y := (Finset.mem_filter.mp hx).2
      rw [← hxy, hτrep]
    have hR : (∑ y ∈ R, (∑ x, if rep x = y then ε x else 0) * τ y) =
        ∑ b, a b * (s' b).powerTrace v (fun h => hv (hS' b h)) k := by
      rw [← Finset.sum_coe_sort R]
      exact (Equiv.sum_comp eR (fun y : R =>
        (∑ x, if rep x = y.val then ε x else 0) * τ y.val)).symm
    rw [← hR, ← hgroup, hsum0]
  have hzero := hind R.card c' s' hc' hinj S hS' a hrel
  -- equal fibre cardinalities
  have hcard : ∀ y, Fintype.card {i // rep (Sum.inl i) = y} =
      Fintype.card {j // rep (Sum.inr j) = y} := by
    intro y
    by_cases hy : y ∈ R
    · have hb := hzero (eR.symm ⟨y, hy⟩)
      have hval : (eR (eR.symm ⟨y, hy⟩)).val = y := by rw [Equiv.apply_symm_apply]
      have ha : a (eR.symm ⟨y, hy⟩) =
          (Fintype.card {i // rep (Sum.inl i) = y} : ℂ) -
            Fintype.card {j // rep (Sum.inr j) = y} := by
        change (∑ x, if rep x = (eR (eR.symm ⟨y, hy⟩)).val then ε x else 0) = _
        rw [hval]
        exact sum_sign_fiber rep y
      rw [ha, sub_eq_zero] at hb
      exact_mod_cast hb
    · have h1 : IsEmpty {i // rep (Sum.inl i) = y} :=
        ⟨fun i => hy (i.2 ▸ Finset.mem_image_of_mem rep (Finset.mem_univ _))⟩
      have h2 : IsEmpty {j // rep (Sum.inr j) = y} :=
        ⟨fun j => hy (j.2 ▸ Finset.mem_image_of_mem rep (Finset.mem_univ _))⟩
      rw [Fintype.card_eq_zero, Fintype.card_eq_zero]
  obtain ⟨e, he⟩ := exists_equiv_of_card_fiber_eq (fun i => rep (Sum.inl i))
    (fun j => rep (Sum.inr j)) hcard
  refine ⟨e, fun i => ?_⟩
  have hgi : g (Sum.inr (e i)) = g (Sum.inl i) := (hrep_iff _ _).mp (he i)
  exact hgi.symm

/-- **Constituent recovery from trace independence.** Jacquet–Shalika (1981), II, the
numerical step of Theorem 4.4, from Theorem 4.2. -/
theorem cuspidalPowerTraceConstituentRecovery_of_independence
    (hind : CuspidalPowerTraceIndependenceStatement.{uF, uV}) :
    CuspidalPowerTraceConstituentRecoveryStatement.{uF, uV} := fun F _ _ _ =>
  cuspidalPowerTraceConstituentRecoveryAt_of_independenceAt (hind F)

/-- **The Euler form of constituent recovery from the trace form, over one field.** -/
theorem cuspidalEulerConstituentRecoveryAt_of_powerTraceRecoveryAt {F : Type uF} [Field F]
    [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hrec : CuspidalPowerTraceConstituentRecoveryAt.{uF, uV} F) :
    CuspidalEulerConstituentRecoveryAt.{uF, uV} F := by
  intro p q c d s t hs ht hE
  exact hrec p q c d s t hs ht (SameEulerPolynomials.samePowerTraces hE)

/-- **The Euler form of constituent recovery from the trace form.** -/
theorem cuspidalEulerConstituentRecovery_of_powerTraceRecovery
    (hrec : CuspidalPowerTraceConstituentRecoveryStatement.{uF, uV}) :
    CuspidalEulerConstituentRecoveryStatement.{uF, uV} := fun F _ _ _ =>
  cuspidalEulerConstituentRecoveryAt_of_powerTraceRecoveryAt (hrec F)

/-- The numerical recovery argument of Jacquet–Shalika II, Theorem 4.4, reduces
all three rigidity conjuncts to their first one, the trace independence of Theorem 4.2. -/
def CuspidalSpectralRigidityReductionStatement : Prop :=
  CuspidalPowerTraceIndependenceStatement.{uF, uV} → CuspidalSpectralRigidityStatement.{uF, uV}

/-- Assemble trace independence and the two numerical recovery implications. -/
theorem cuspidalSpectralRigidity_of_independence :
    CuspidalSpectralRigidityReductionStatement.{uF, uV} := by
  intro hind
  have hrec := cuspidalPowerTraceConstituentRecovery_of_independence hind
  exact ⟨hind, hrec, cuspidalEulerConstituentRecovery_of_powerTraceRecovery hrec⟩

end Langlands.Automorphic.Unramified
