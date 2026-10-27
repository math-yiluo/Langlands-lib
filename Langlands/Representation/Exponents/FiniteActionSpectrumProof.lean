import Langlands.Representation.Exponents.FiniteActionSpectrumStatement
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Finite spectrum of a commutative action with finite operator span

The operators of the action span a finite-dimensional commutative algebra.
Its finitely many complex characters, its nilpotent Jacobson radical and
separating elements give a uniform decomposition of the carrier.
-/

noncomputable section

namespace Langlands

universe uR uA uV

namespace FiniteActionSpectrum

section Algebra

variable {R : Type uR} [CommRing R] [Algebra ℂ R] [Module.Finite ℂ R]

/-- Every maximal ideal of a finite-dimensional commutative complex algebra is
the kernel of a complex character. -/
theorem exists_algHom_ker_eq (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[ℂ] ℂ, RingHom.ker φ = m := by
  have : Module.Finite ℂ (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℂ m)
  have : Algebra.IsIntegral ℂ (R ⧸ m) := Algebra.IsIntegral.of_finite ℂ _
  let e : ℂ ≃ₐ[ℂ] R ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(e.symm : R ⧸ m →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

omit [Module.Finite ℂ R] in
/-- Two complex characters with the same kernel coincide. -/
theorem algHom_eq_of_ker_eq {φ ψ : R →ₐ[ℂ] ℂ} (h : RingHom.ker φ = RingHom.ker ψ) :
    φ = ψ := by
  ext x
  have hx : x - algebraMap ℂ R (φ x) ∈ RingHom.ker ψ := by
    rw [← h, RingHom.mem_ker]
    simp
  rw [RingHom.mem_ker] at hx
  simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hx
  exact hx.symm

/-- A finite-dimensional commutative complex algebra has finitely many complex
characters. -/
theorem finite_algHom : Finite (R →ₐ[ℂ] ℂ) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  have : Finite {I : Ideal R // I.IsMaximal} :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).to_subtype
  refine Finite.of_injective
    (fun φ : R →ₐ[ℂ] ℂ => (⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ
      (fun c => ⟨algebraMap ℂ R c, by simp⟩)⟩ : {I : Ideal R // I.IsMaximal})) ?_
  intro φ ψ hφψ
  exact algHom_eq_of_ker_eq (congrArg Subtype.val hφψ)

omit [Module.Finite ℂ R] in
/-- Two distinct complex characters are separated by an element. -/
theorem exists_separating (φ ψ : R →ₐ[ℂ] ℂ) (h : φ ≠ ψ) :
    ∃ r : R, φ r = 1 ∧ ψ r = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, φ s ≠ ψ s := by
    by_contra! H
    exact h (AlgHom.ext H)
  refine ⟨(φ s - ψ s)⁻¹ • (s - algebraMap ℂ R (ψ s)), ?_, ?_⟩
  · simp only [map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hs)
  · simp

/-- Uniform decomposition data: elements whose sum is a unit and which are
annihilated by a fixed power of the corresponding character kernel. -/
theorem exists_decomposition [Fintype (R →ₐ[ℂ] ℂ)] :
    ∃ (N : ℕ) (h : (R →ₐ[ℂ] ℂ) → R),
      IsUnit (∑ φ, h φ) ∧ ∀ φ, ∀ y ∈ RingHom.ker φ ^ N, y * h φ = 0 := by
  classical
  have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  let J : Ideal R := ⨅ φ : R →ₐ[ℂ] ℂ, RingHom.ker φ
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    refine le_sInf ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq m
    rw [← hφ]
    exact iInf_le _ φ
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hN' : Ideal.jacobson (⊥ : Ideal R) ^ (N + 1) = ⊥ := by
    rw [pow_succ, hN, zero_mul]
    rfl
  choose r hr using fun (φ ψ : R →ₐ[ℂ] ℂ) (h : φ ≠ ψ) => exists_separating φ ψ h
  let g : (R →ₐ[ℂ] ℂ) → R := fun φ => ∏ ψ : {ψ // ψ ≠ φ}, r φ ψ ψ.2.symm
  have hg_self : ∀ φ : R →ₐ[ℂ] ℂ, φ (g φ) = 1 := by
    intro φ
    simp only [g, map_prod]
    exact Finset.prod_eq_one fun ψ _ => (hr φ ψ ψ.2.symm).1
  have hg_other : ∀ φ ψ : R →ₐ[ℂ] ℂ, ψ ≠ φ → ψ (g φ) = 0 := by
    intro φ ψ hψ
    simp only [g, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨ψ, hψ⟩) (hr φ ψ hψ.symm).2
  refine ⟨N + 1, fun φ => g φ ^ (N + 1), ?_, ?_⟩
  · have hmem : (∑ φ, g φ ^ (N + 1)) - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
      apply hJ
      rw [Submodule.mem_iInf]
      intro ψ
      rw [RingHom.mem_ker, map_sub, map_one, map_sum, Finset.sum_eq_single ψ]
      · rw [map_pow, hg_self, one_pow, sub_self]
      · intro φ _ hφ
        rw [map_pow, hg_other φ ψ (Ne.symm hφ), zero_pow (Nat.succ_ne_zero N)]
      · intro hψ
        exact absurd (Finset.mem_univ ψ) hψ
    simpa using (Ideal.mem_jacobson_bot.mp hmem) 1
  · intro φ y hy
    have h1 : RingHom.ker φ * Ideal.span {g φ} ≤ J := by
      rw [Ideal.mul_le]
      intro x hx z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [Submodule.mem_iInf]
      intro ψ
      rw [RingHom.mem_ker] at hx ⊢
      by_cases hψ : ψ = φ
      · subst hψ
        simp [hx]
      · simp [hg_other φ ψ hψ]
    have h2 : y * g φ ^ (N + 1) ∈ (RingHom.ker φ * Ideal.span {g φ}) ^ (N + 1) := by
      rw [mul_pow]
      exact Ideal.mul_mem_mul hy (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
    have h3 := Ideal.pow_right_mono (h1.trans hJ) (N + 1) h2
    rw [hN'] at h3
    exact (Submodule.mem_bot R).mp h3

end Algebra

section Representation

variable {A : Type uA} [CommGroup A] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {R : Type uR} [CommRing R] [Algebra ℂ R]

/-- The character of `A` obtained by composing a complex character of an
operator algebra with the action. -/
def algebraCharacter (ρ' : A →* R) (φ : R →ₐ[ℂ] ℂ) : A →* ℂˣ :=
  (φ.toRingHom.toMonoidHom.comp ρ').toHomUnits

@[simp]
theorem algebraCharacter_apply (ρ' : A →* R) (φ : R →ₐ[ℂ] ℂ) (a : A) :
    ((algebraCharacter ρ' φ a : ℂˣ) : ℂ) = φ (ρ' a) :=
  rfl

/-- Vectors annihilated by powers of `T - α` and of `T - β` vanish when `α ≠ β`. -/
theorem eq_zero_of_pow_sub_smul {T : Module.End ℂ V} {α β : ℂ} (hαβ : α ≠ β)
    {k l : ℕ} {w : V} (hα : ((T - α • 1) ^ k) w = 0) (hβ : ((T - β • 1) ^ l) w = 0) :
    w = 0 := by
  have h1 : w ∈ T.genEigenspace α k :=
    Module.End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr hα)
  have h2 : w ∈ T.genEigenspace β l :=
    Module.End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr hβ)
  have := (Module.End.disjoint_genEigenspace T hαβ (k : ℕ∞) (l : ℕ∞)).le_bot
    (Submodule.mem_inf.mpr ⟨h1, h2⟩)
  simpa using this

theorem subrepresentation_mem_bot_iff {ρ : Representation ℂ A V} {v : V} :
    v ∈ (⊥ : Subrepresentation ρ) ↔ v = 0 :=
  Submodule.mem_bot ℂ

theorem subrepresentation_exists_ne_zero {ρ : Representation ℂ A V}
    {P : Subrepresentation ρ} (hP : P ≠ ⊥) : ∃ v ∈ P, v ≠ 0 := by
  by_contra! h
  exact hP (eq_bot_iff.mpr fun v hv => subrepresentation_mem_bot_iff.mpr (h v hv))

/-- The spectral conclusions for a representation factoring through a
finite-dimensional commutative algebra spanned by the action. -/
theorem spectrum_of_algebra [TopologicalSpace A] [Module.Finite ℂ R]
    (ρ : Representation ℂ A V) (ι : R →ₐ[ℂ] Module.End ℂ V) (ρ' : A →* R)
    (hι : ∀ a, ι (ρ' a) = ρ a) (hspan : Submodule.span ℂ (Set.range ρ') = ⊤)
    (hloc : IsLocallyConstant ρ') :
      {χ : A →* ℂˣ |
        IsOpen (χ.ker : Set A) ∧
          commutativeCharacterSpace ρ χ 1 ≠ ⊥}.Finite ∧
      (∀ χ : A →* ℂˣ,
        (IsOpen (χ.ker : Set A) ∧
          commutativeCharacterSpace ρ χ 1 ≠ ⊥) →
          commutativeCharacterNilpotenceIndex ρ χ < ⊤) ∧
      (⨆ (χ : A →* ℂˣ)
          (_ : IsOpen (χ.ker : Set A) ∧
            commutativeCharacterSpace ρ χ 1 ≠ ⊥),
        (generalizedCommutativeCharacterSpace ρ χ).toSubmodule) = ⊤ := by
  classical
  have : Finite (R →ₐ[ℂ] ℂ) := finite_algHom
  let : Fintype (R →ₐ[ℂ] ℂ) := Fintype.ofFinite _
  obtain ⟨N, h, hu, hann⟩ := exists_decomposition (R := R)
  let w : R := ((hu.unit⁻¹ : Rˣ) : R)
  have hcomm : ∀ (r : R) (a : A), Commute (ι r) (ρ a) := by
    intro r a
    rw [← hι]
    exact (Commute.all r (ρ' a)).map ι
  have hcommpow : ∀ (r : R) (a : A) (c : ℂ) (k : ℕ) (v : V),
      ((ρ a - c • 1) ^ k) (ι r v) = ι r (((ρ a - c • 1) ^ k) v) := by
    intro r a c k v
    have hC : Commute (ι r) ((ρ a - c • 1) ^ k) :=
      ((hcomm r a).sub_right ((Commute.one_right _).smul_right c)).pow_right k
    exact LinearMap.congr_fun hC.eq.symm v
  have hdef : ∀ (φ : R →ₐ[ℂ] ℂ) (a : A),
      ρ a - ((algebraCharacter ρ' φ a : ℂˣ) : ℂ) • 1 =
        ι (ρ' a - algebraMap ℂ R (φ (ρ' a))) := by
    intro φ a
    rw [map_sub, AlgHom.commutes, hι, Algebra.algebraMap_eq_smul_one, algebraCharacter_apply]
  have hdef_ker : ∀ (φ : R →ₐ[ℂ] ℂ) (a : A),
      ρ' a - algebraMap ℂ R (φ (ρ' a)) ∈ RingHom.ker φ := by
    intro φ a
    simp [RingHom.mem_ker]
  have hbound : ∀ (φ : R →ₐ[ℂ] ℂ) (a : A) (v : V),
      ((ρ a - ((algebraCharacter ρ' φ a : ℂˣ) : ℂ) • 1) ^ N) (ι (h φ) v) = 0 := by
    intro φ a v
    rw [hdef φ a, ← map_pow, ← Module.End.mul_apply, ← map_mul,
      hann φ _ (Ideal.pow_mem_pow (hdef_ker φ a) N), map_zero, LinearMap.zero_apply]
  have hdecomp : ∀ v : V, v = ∑ φ, ι (h φ) (ι w v) := by
    intro v
    have h1 : (∑ φ, h φ) * w = 1 := hu.mul_val_inv
    calc v = ι ((∑ φ, h φ) * w) v := by rw [h1, map_one, Module.End.one_apply]
      _ = ∑ φ, ι (h φ) (ι w v) := by
        rw [map_mul, Module.End.mul_apply, map_sum, LinearMap.sum_apply]
  have hsep : ∀ φ ψ : R →ₐ[ℂ] ℂ, φ ≠ ψ → algebraCharacter ρ' φ ≠ algebraCharacter ρ' ψ := by
    intro φ ψ hne heq
    apply hne
    apply AlgHom.toLinearMap_injective
    refine LinearMap.ext_on_range hspan fun a => ?_
    have := congrArg (fun f : A →* ℂˣ => ((f a : ℂˣ) : ℂ)) heq
    simpa using this
  have hstable : ∀ (θ : A →* ℂˣ) (r : R) (v : V),
      v ∈ generalizedCommutativeCharacterSpace ρ θ →
        ι r v ∈ generalizedCommutativeCharacterSpace ρ θ := by
    intro θ r v hv
    obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace ρ θ v).mp hv
    exact (mem_generalizedCommutativeCharacterSpace ρ θ _).mpr
      ⟨k, fun a => by rw [hcommpow, hk a, map_zero]⟩
  have hkill : ∀ (θ : A →* ℂˣ) (ψ : R →ₐ[ℂ] ℂ) (v : V),
      v ∈ generalizedCommutativeCharacterSpace ρ θ →
        θ ≠ algebraCharacter ρ' ψ → ι (h ψ) v = 0 := by
    intro θ ψ v hv hne
    obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace ρ θ v).mp hv
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hne
    refine eq_zero_of_pow_sub_smul (T := ρ a) (fun heq => ha (Units.ext heq))
      (k := k) (l := N) ?_ (hbound ψ a v)
    rw [hcommpow, hk a, map_zero]
  have hgen1 : ∀ (θ : A →* ℂˣ) (v : V), v ∈ commutativeCharacterSpace ρ θ 1 →
      v ∈ generalizedCommutativeCharacterSpace ρ θ := by
    intro θ v hv
    exact (mem_generalizedCommutativeCharacterSpace ρ θ v).mpr
      ⟨1, (mem_commutativeCharacterSpace ρ θ 1 v).mp hv⟩
  have hocc : ∀ θ : A →* ℂˣ, commutativeCharacterSpace ρ θ 1 ≠ ⊥ →
      ∃ φ, θ = algebraCharacter ρ' φ := by
    intro θ hθ
    obtain ⟨v, hv, hv0⟩ := subrepresentation_exists_ne_zero hθ
    by_contra! hne
    apply hv0
    rw [hdecomp v]
    exact Finset.sum_eq_zero fun ψ _ =>
      hkill θ ψ _ (hstable θ w v (hgen1 θ v hv)) (hne ψ)
  have hopen : ∀ φ : R →ₐ[ℂ] ℂ, IsOpen ((algebraCharacter ρ' φ).ker : Set A) := by
    intro φ
    convert (hloc.comp φ).isOpen_fiber 1 using 1
    ext a
    simp [MonoidHom.mem_ker, Units.ext_iff]
  have heigen : ∀ (φ : R →ₐ[ℂ] ℂ) (t : V), t ≠ 0 →
      (∀ y ∈ RingHom.ker φ ^ N, ι y t = 0) →
        ∃ e : V, e ≠ 0 ∧ ∀ a, ρ a e = ((algebraCharacter ρ' φ a : ℂˣ) : ℂ) • e := by
    intro φ t ht hN
    have hex : ∃ j, ∀ y ∈ RingHom.ker φ ^ j, ι y t = 0 := ⟨N, hN⟩
    obtain ⟨j, hj, hmin⟩ : ∃ j, (∀ y ∈ RingHom.ker φ ^ j, ι y t = 0) ∧
        ∀ i < j, ¬ ∀ y ∈ RingHom.ker φ ^ i, ι y t = 0 :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply ht
      have := hj 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
      simpa using this
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hnot := hmin i (Nat.lt_succ_self i)
    push Not at hnot
    obtain ⟨y, hy, hyt⟩ := hnot
    refine ⟨ι y t, hyt, fun a => ?_⟩
    have hmem : (ρ' a - algebraMap ℂ R (φ (ρ' a))) * y ∈ RingHom.ker φ ^ (i + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hdef_ker φ a) hy
    have h0 := hj _ hmem
    rw [map_mul, Module.End.mul_apply, ← hdef, LinearMap.sub_apply, sub_eq_zero] at h0
    simpa using h0
  refine ⟨?_, ?_, ?_⟩
  · refine (Set.finite_range (algebraCharacter (R := R) ρ')).subset ?_
    rintro θ ⟨-, hθ⟩
    obtain ⟨φ, rfl⟩ := hocc θ hθ
    exact ⟨φ, rfl⟩
  · rintro θ ⟨-, hθ⟩
    obtain ⟨φ, rfl⟩ := hocc θ hθ
    have hle : commutativeCharacterNilpotenceIndex ρ (algebraCharacter ρ' φ) ≤ (N : ℕ∞) := by
      rw [commutativeCharacterNilpotenceIndex_le_iff]
      intro v hv
      have hv' : v = ι (h φ) (ι w v) := by
        conv_lhs => rw [hdecomp v]
        exact Finset.sum_eq_single φ
          (fun ψ _ hψ => hkill _ ψ _ (hstable _ w v hv) (hsep φ ψ (Ne.symm hψ)))
          (fun hφ => absurd (Finset.mem_univ φ) hφ)
      rw [mem_commutativeCharacterSpace]
      intro a
      rw [hv']
      exact hbound φ a (ι w v)
    exact lt_of_le_of_lt hle (ENat.natCast_lt_top N)
  · rw [eq_top_iff]
    intro v _
    rw [hdecomp v]
    refine Submodule.sum_mem _ fun φ _ => ?_
    by_cases ht0 : ι (h φ) (ι w v) = 0
    · rw [ht0]
      exact Submodule.zero_mem _
    · have hocc' : IsOpen ((algebraCharacter ρ' φ).ker : Set A) ∧
          commutativeCharacterSpace ρ (algebraCharacter ρ' φ) 1 ≠ ⊥ := by
        refine ⟨hopen φ, ?_⟩
        obtain ⟨e, he0, he⟩ := heigen φ _ ht0 (fun y hy => by
          rw [← Module.End.mul_apply, ← map_mul, hann φ y hy, map_zero, LinearMap.zero_apply])
        intro hbot
        apply he0
        have hmem : e ∈ commutativeCharacterSpace ρ (algebraCharacter ρ' φ) 1 :=
          (mem_commutativeCharacterSpace_one ρ _ e).mpr he
        rw [hbot] at hmem
        exact subrepresentation_mem_bot_iff.mp hmem
      have htmem : ι (h φ) (ι w v) ∈ generalizedCommutativeCharacterSpace ρ (algebraCharacter ρ' φ) :=
        (mem_generalizedCommutativeCharacterSpace ρ _ _).mpr ⟨N, fun a => hbound φ a (ι w v)⟩
      exact Submodule.mem_iSup_of_mem (algebraCharacter ρ' φ)
        (Submodule.mem_iSup_of_mem hocc' htmem)

end Representation

end FiniteActionSpectrum

open FiniteActionSpectrum in
/-- The finite spectrum, uniform nilpotence and spanning of generalized
components for a commutative action with finite operator span. -/
theorem finiteActionCommutativeSpectrum :
    FiniteActionCommutativeSpectrumStatement.{uA,uV} := by
  intro A _ _ V _ _ ρ hfin hloc
  let S : Submodule ℂ (Module.End ℂ V) := Submodule.span ℂ (Set.range ρ)
  have hmem : ∀ a, ρ a ∈ S := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hone : (1 : Module.End ℂ V) ∈ S := by simpa using hmem 1
  have hmulρ : ∀ a, ∀ x ∈ S, ρ a * x ∈ S ∧ x * ρ a = ρ a * x := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [← map_mul]
        exact hmem (a * b)
      · rw [← map_mul, ← map_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [mul_add]
        exact S.add_mem hx.1 hy.1
      · rw [mul_add, add_mul, hx.2, hy.2]
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [mul_smul_comm]
        exact S.smul_mem c hx.1
      · rw [mul_smul_comm, smul_mul_assoc, hx.2]
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S ∧ x * y = y * x := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact ⟨(hmulρ a y hy).1, (hmulρ a y hy).2.symm⟩
    | zero => simp
    | add x z _ _ hx hz =>
      refine ⟨?_, ?_⟩
      · rw [add_mul]
        exact S.add_mem hx.1 hz.1
      · rw [add_mul, mul_add, hx.2, hz.2]
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [smul_mul_assoc]
        exact S.smul_mem c hx.1
      · rw [smul_mul_assoc, mul_smul_comm, hx.2]
  let B : Subalgebra ℂ (Module.End ℂ V) :=
    S.toSubalgebra hone (fun x y hx hy => (hmul x y hx hy).1)
  let : CommRing B :=
    { (inferInstance : Ring B) with
      mul_comm := fun x y => Subtype.ext (hmul x y x.2 y.2).2 }
  have : Module.Finite ℂ B := by
    have : Module.Finite ℂ (Subalgebra.toSubmodule B) := by
      rw [Submodule.toSubalgebra_toSubmodule]
      exact hfin
    exact Subalgebra.finiteDimensional_toSubmodule.mp this
  let ρ' : A →* B := ρ.codRestrict B hmem
  have hspan : Submodule.span ℂ (Set.range ρ') = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    change x ∈ S at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy => exact Submodule.smul_mem _ c hy
  have hloc' : IsLocallyConstant ρ' :=
    IsLocallyConstant.desc _ Subtype.val hloc Subtype.val_injective
  exact spectrum_of_algebra ρ B.val ρ' (fun _ => rfl) hspan hloc'

end Langlands
