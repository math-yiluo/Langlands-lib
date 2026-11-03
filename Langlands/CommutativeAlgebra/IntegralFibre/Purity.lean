import Mathlib.RingTheory.Lasker
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # A purity lemma for flat algebras over Noetherian rings -/

open TensorProduct

namespace Langlands.CommutativeAlgebra.IntegralFibre

section SMulInj

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Multiplication by `u` on `S ⊗[R] X` is injective. -/
def SMulInjOn (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (u : S)
    (X : Type*) [AddCommGroup X] [Module R X] : Prop :=
  Function.Injective (fun z : S ⊗[R] X ↦ u • z)

lemma lTensor_smul_comm (u : S) {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (z : S ⊗[R] X) :
    f.lTensor S (u • z) = u • f.lTensor S z := by
  induction z with
  | tmul s x => simp [smul_tmul']
  | add a b ha hb => simp [smul_add, ha, hb]

lemma SMulInjOn.of_subsingleton (u : S) (X : Type*) [AddCommGroup X] [Module R X]
    [Subsingleton X] : SMulInjOn R u X := by
  intro a b _
  exact Subsingleton.elim _ _

lemma SMulInjOn.of_linearEquiv {u : S} {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y) (h : SMulInjOn R u X) : SMulInjOn R u Y := by
  intro a b hab
  apply (e.symm.lTensor S).injective
  apply h
  simp only at hab ⊢
  have key : ∀ z : S ⊗[R] Y, (e.symm.lTensor S) (u • z) = u • (e.symm.lTensor S) z :=
    fun z ↦ lTensor_smul_comm u e.symm.toLinearMap z
  rw [← key, ← key, hab]

variable [Module.Flat R S]

lemma SMulInjOn.of_injective {u : S} {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (hf : Function.Injective f)
    (h : SMulInjOn R u Y) : SMulInjOn R u X := by
  intro a b hab
  apply Module.Flat.lTensor_preserves_injective_linearMap f hf
  apply h
  simp only at hab ⊢
  rw [← lTensor_smul_comm, ← lTensor_smul_comm, hab]

lemma SMulInjOn.of_exact {u : S} {X Y Z : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hX : SMulInjOn R u X) (hZ : SMulInjOn R u Z) : SMulInjOn R u Y := by
  have hX' : ∀ x : S ⊗[R] X, u • x = 0 → x = 0 := fun x hx ↦ hX (by simpa using hx)
  have hZ' : ∀ x : S ⊗[R] Z, u • x = 0 → x = 0 := fun x hx ↦ hZ (by simpa using hx)
  have key : ∀ y : S ⊗[R] Y, u • y = 0 → y = 0 := by
    intro y hy
    have h1 : g.lTensor S y = 0 := hZ' _ (by rw [← lTensor_smul_comm, hy, map_zero])
    obtain ⟨x, rfl⟩ := (Module.Flat.lTensor_exact S hfg y).mp h1
    have h2 : u • x = 0 := by
      apply Module.Flat.lTensor_preserves_injective_linearMap f hf
      rw [lTensor_smul_comm, hy, map_zero]
    rw [hX' x h2, map_zero]
  intro a b hab
  have : u • (a - b) = 0 := by
    simp only at hab
    rw [smul_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ this)

lemma SMulInjOn.prod {u : S} {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (hX : SMulInjOn R u X) (hY : SMulInjOn R u Y) :
    SMulInjOn R u (X × Y) :=
  SMulInjOn.of_exact (LinearMap.inl R X Y) (LinearMap.snd R X Y) LinearMap.inl_injective
    Function.Exact.inl_snd hX hY

omit [Module.Flat R S] in
lemma SMulInjOn.finsupp {u : S} {X : Type*} [AddCommGroup X] [Module R X] (ι : Type*)
    (hX : SMulInjOn R u X) : SMulInjOn R u (ι →₀ X) := by
  classical
  intro a b hab
  simp only at hab
  apply (finsuppRight R S S X ι).injective
  ext i
  apply hX
  have := congrArg (fun z ↦ finsuppRight R S S X ι z i) hab
  simpa only [LinearEquiv.map_smul, Finsupp.smul_apply] using this

omit [Module.Flat R S] in
lemma SMulInjOn.of_isTorsionBySet_maximalIdeal {u : S} (p : Ideal R) [p.IsPrime]
    {W : Type*} [AddCommGroup W] [Module R W] [Module (Localization.AtPrime p) W]
    [IsScalarTower R (Localization.AtPrime p) W]
    (hW : Module.IsTorsionBySet (Localization.AtPrime p) W
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)))
    (hκ : SMulInjOn R u p.ResidueField) :
    SMulInjOn R u W := by
  let : Module p.ResidueField W := hW.module
  have : IsScalarTower R p.ResidueField W := hW.isScalarTower
  let b := Module.Free.chooseBasis p.ResidueField W
  exact (hκ.finsupp _).of_linearEquiv (b.repr.restrictScalars R).symm

/-- Modules over `Rₚ` killed by a power of the maximal ideal. -/
lemma SMulInjOn.of_pow_maximalIdeal_smul_eq_zero {u : S} (p : Ideal R) [p.IsPrime]
    (hκ : SMulInjOn R u p.ResidueField) (e : ℕ) :
    ∀ (W : Type*) [AddCommGroup W] [Module R W] [Module (Localization.AtPrime p) W]
      [IsScalarTower R (Localization.AtPrime p) W],
      (∀ a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ e, ∀ w : W, a • w = 0) →
      SMulInjOn R u W := by
  induction e with
  | zero =>
    intro W _ _ _ _ hW
    have : Subsingleton W := ⟨fun a b ↦ by
      rw [← one_smul (Localization.AtPrime p) a, ← one_smul (Localization.AtPrime p) b,
        hW 1 (by simp), hW 1 (by simp)]⟩
    exact SMulInjOn.of_subsingleton u W
  | succ e ih =>
    intro W _ _ _ _ hW
    let m := IsLocalRing.maximalIdeal (Localization.AtPrime p)
    let W' : Submodule (Localization.AtPrime p) W := (m ^ e) • ⊤
    have hW' : Module.IsTorsionBySet (Localization.AtPrime p) W' m := by
      rintro ⟨x, hx⟩ ⟨a, ha⟩
      apply Subtype.ext
      simp only [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero]
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro b hb w _
        rw [smul_smul]
        exact hW _ (by rw [pow_succ']; exact Ideal.mul_mem_mul ha hb) w
      · intro x y hx hy
        rw [smul_add, hx, hy, add_zero]
    have h1 : SMulInjOn R u W' := SMulInjOn.of_isTorsionBySet_maximalIdeal p hW' hκ
    have h2 : SMulInjOn R u (W ⧸ W') := by
      apply ih
      intro a ha w
      induction w using Submodule.Quotient.induction_on with
      | H w =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact SMulInjOn.of_exact (W'.subtype.restrictScalars R) (W'.mkQ.restrictScalars R)
      Subtype.val_injective (by
        intro w
        simp [Submodule.Quotient.mk_eq_zero]) h1 h2

/-- A coprimary module: elements outside `p` act injectively and a power of `p` kills it. -/
lemma SMulInjOn.of_coprimary {u : S} (p : Ideal R) [p.IsPrime]
    (hκ : SMulInjOn R u p.ResidueField) {E : Type*} [AddCommGroup E] [Module R E]
    (hinj : ∀ r ∉ p, ∀ x : E, r • x = 0 → x = 0) (e : ℕ)
    (hkill : ∀ r ∈ p ^ e, ∀ x : E, r • x = 0) : SMulInjOn R u E := by
  let f := LocalizedModule.mkLinearMap p.primeCompl E
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl f).mp hx
    exact hinj c c.2 x hc
  apply SMulInjOn.of_injective f hf
  apply SMulInjOn.of_pow_maximalIdeal_smul_eq_zero p hκ e
  intro a ha w
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r, hr, rfl⟩ := ha
    induction w using LocalizedModule.induction_on with
    | h m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, hkill r hr m, LocalizedModule.zero_mk]
  | zero => exact zero_smul _ w
  | add a b _ _ ha hb => rw [add_smul, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_eq_mul, mul_smul, ha, smul_zero]

/-- **Purity lemma.** Over a Noetherian ring, multiplication by `u` is injective on
`S ⊗[R] N` for a finite module `N` as soon as it is injective on the fibres of `S` at the
associated primes of `N`. -/
theorem SMulInjOn.of_associatedPrimes [IsNoetherianRing R] {u : S} {N : Type*}
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : ∀ (p : Ideal R) [p.IsPrime], p ∈ associatedPrimes R N → SMulInjOn R u p.ResidueField) :
    SMulInjOn R u N := by
  obtain ⟨t, ht⟩ := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition
    (Submodule.isLasker R N) (⊥ : Submodule R N)
  have primary : ∀ Q ∈ t, SMulInjOn R u (N ⧸ Q) := by
    intro Q hQ
    have hprim := ht.primary hQ
    have : (Q.colon Set.univ).radical.IsPrime := hprim.isPrime_radical_colon
    have hass : (Q.colon Set.univ).radical ∈ associatedPrimes R N := ht.mem_associatedPrimes hQ
    obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_refl _)
      (IsNoetherian.noetherian (Q.colon Set.univ).radical)
    refine SMulInjOn.of_coprimary _ (h _ hass) ?_ e ?_
    · intro r hr x hx
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.Quotient.mk_eq_zero]
        exact (hprim.mem_or_mem hx).resolve_right hr
    · intro r hr x
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_colon.mp (he hr) x (Set.mem_univ x)
  have key : ∀ t' : Finset (Submodule R N), t' ⊆ t → SMulInjOn R u (N ⧸ t'.inf id) := by
    intro t'
    induction t' using Finset.induction_on with
    | empty =>
      intro _
      show SMulInjOn R u (N ⧸ (⊤ : Submodule R N))
      exact SMulInjOn.of_subsingleton u _
    | insert Q t' hQ ih =>
      intro hsub
      rw [Finset.inf_insert]
      have h1 := primary Q (hsub (Finset.mem_insert_self _ _))
      have h2 := ih ((Finset.subset_insert _ _).trans hsub)
      refine (h1.prod h2).of_injective
        ((id Q ⊓ t'.inf id).liftQ ((id Q).mkQ.prod (t'.inf id).mkQ) ?_) ?_
      · rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
      · rw [← LinearMap.ker_eq_bot]
        exact Submodule.ker_liftQ_eq_bot' _ _ (by
          rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ])
  have h0 := key t subset_rfl
  rw [ht.inf_eq] at h0
  refine h0.of_injective (Submodule.mkQ ⊥) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]

end SMulInj

end Langlands.CommutativeAlgebra.IntegralFibre
