import Langlands.Algebra.GenericIrreducibilityHypersurface
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.MvPolynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra.GenericIrreducibilitySpreading

theorem add_pow_expChar_pow_of_ringHom
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    (f : R →+* A) (q e : ℕ) [ExpChar R q] (a b : A) :
    (a + b) ^ q ^ e = a ^ q ^ e + b ^ q ^ e := by
  nontriviality A
  cases ‹ExpChar R q› with
  | zero => simp
  | prime hq =>
    have : CharP A q := CharP.of_ringHom_of_ne_zero f q hq.ne_zero
    have : ExpChar A q := ExpChar.prime hq
    exact add_pow_expChar_pow a b q e

theorem tensor_uniform_power_containment
    {R : Type u} {C : Type v} {K : Type w}
    [CommRing R] [IsDomain R] [CommRing C] [CommRing K]
    [Algebra R C] [Algebra R K]
    (S : Subalgebra R C) (T : Subalgebra K (K ⊗[R] C))
    (g : C) (hg : g ∈ S) (q e : ℕ) [ExpChar R q]
    (hS : ∀ c ∈ S, Algebra.TensorProduct.includeRight (A := K) c ∈ T)
    (hrad : ∀ c : C, ∃ m : ℕ, (g ^ m * c) ^ q ^ e ∈ S) :
    ∀ a : K ⊗[R] C, ∃ m : ℕ,
      ((Algebra.TensorProduct.includeRight (A := K) g) ^ m * a) ^ q ^ e ∈ T := by
  let j : C →ₐ[R] K ⊗[R] C := Algebra.TensorProduct.includeRight
  have hgT : j g ∈ T := hS g hg
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul k c =>
    obtain ⟨m, hm⟩ := hrad c
    refine ⟨m, ?_⟩
    have heq : (j g ^ m * (k ⊗ₜ[R] c)) ^ q ^ e =
        algebraMap K (K ⊗[R] C) (k ^ q ^ e) * j ((g ^ m * c) ^ q ^ e) := by
      simp only [map_pow, map_mul, j, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_pow,
        Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, mul_one,
        Algebra.algebraMap_self_apply]
    rw [heq]
    exact mul_mem (T.algebraMap_mem _) (hS _ hm)
  | add a b ha hb =>
    obtain ⟨m₁, h₁⟩ := ha
    obtain ⟨m₂, h₂⟩ := hb
    refine ⟨m₁ + m₂, ?_⟩
    have heq : (j g ^ (m₁ + m₂) * (a + b)) ^ q ^ e =
        (j g ^ m₂) ^ q ^ e * (j g ^ m₁ * a) ^ q ^ e +
        (j g ^ m₁) ^ q ^ e * (j g ^ m₂ * b) ^ q ^ e := by
      rw [mul_add, add_pow_expChar_pow_of_ringHom
        (algebraMap R (K ⊗[R] C)), ← mul_pow, ← mul_pow]
      ring
    rw [heq]
    exact add_mem (mul_mem (pow_mem (pow_mem hgT _) _) h₁)
      (mul_mem (pow_mem (pow_mem hgT _) _) h₂)

theorem tensor_nontrivial_of_comap_surjective
    {R B K : Type*} [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra R K]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) :
    Nontrivial (K ⊗[R] B) := by
  let p : Ideal R := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have hunit : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    exact isUnit_iff_ne_zero.mpr hr
  let f : p.ResidueField →ₐ[R] K :=
    Ideal.ResidueField.liftₐ p (Algebra.ofId R K) le_rfl hunit
  let : Algebra p.ResidueField K := f.toRingHom.toAlgebra
  have : IsScalarTower R p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have : Nontrivial (p.ResidueField ⊗[R] B) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap ⟨p, inferInstance⟩).mpr (h _)
  have : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[R] B)) := inferInstance
  exact (Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K B).symm.toEquiv.nontrivial

theorem tensor_comap_surjective
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (S ⊗[R] B))) := by
  intro p
  have : Nontrivial (p.asIdeal.ResidueField ⊗[R] B) :=
    tensor_nontrivial_of_comap_surjective h
  have : Nontrivial (p.asIdeal.ResidueField ⊗[S] (S ⊗[R] B)) :=
    (Algebra.TensorProduct.cancelBaseChange R S p.asIdeal.ResidueField
      p.asIdeal.ResidueField B).toEquiv.nontrivial
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp inferInstance

theorem tensor_algebraMap_injective_of_comap_surjective
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsReduced S]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) :
    Function.Injective (algebraMap S (S ⊗[R] B)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap S (S ⊗[R] B))).mp (tensor_comap_surjective h).denseRange
  simpa only [(nilradical_eq_bot_iff (R := S)).mpr inferInstance] using hker

theorem tensor_algebraMap_injective_of_integral_after_away
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsReduced T]
    (hinj : Function.Injective (algebraMap R S)) (r : R)
    (hr : IsUnit (algebraMap R T r))
    (hint : ∀ s : S, ∃ n : ℕ, IsIntegral R (r ^ n • s)) :
    Function.Injective (algebraMap T (T ⊗[R] S)) := by
  classical
  let Rr := Localization.Away r
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
  have : IsLocalization.Away (algebraMap R S r) Sr := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) Sr)
  have hlocinj : Function.Injective (algebraMap Rr Sr) :=
    localizationAlgebra_injective Rr Sr hinj
  have hinv : algebraMap Rr Sr (IsLocalization.Away.invSelf r) *
      algebraMap R Sr r = 1 := by
    rw [IsScalarTower.algebraMap_apply R Rr Sr, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  have hnum : ∀ s : S, IsIntegral Rr (algebraMap S Sr s) := by
    intro s
    obtain ⟨n, hn⟩ := hint s
    apply IsIntegral.of_mul_unit (r := IsLocalization.Away.invSelf r ^ n)
      (y := algebraMap R Sr r ^ n)
    · rw [map_pow, ← mul_pow, hinv, one_pow]
    · have h := (hn.map (IsScalarTower.toAlgHom R S Sr)).tower_top (A := Rr)
      change IsIntegral Rr (algebraMap S Sr (r ^ n • s)) at h
      simpa only [Algebra.smul_def, map_mul, map_pow,
        ← IsScalarTower.algebraMap_apply R S Sr, mul_comm] using h
  have hlocint : (algebraMap Rr Sr).IsIntegral := by
    intro x
    obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (algebraMap R S r) x
    apply IsIntegral.of_mul_unit (r := IsLocalization.Away.invSelf r ^ n)
      (y := algebraMap R Sr r ^ n)
    · rw [map_pow, ← mul_pow, hinv, one_pow]
    · rw [IsScalarTower.algebraMap_apply R S Sr, hs]
      exact hnum s
  let f : Rr →+* T := IsLocalization.Away.lift r hr
  let : Algebra Rr T := f.toAlgebra
  have : IsScalarTower R Rr T :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.Away.lift_eq r hr a).symm)
  let Q := T ⊗[Rr] Sr
  have hQ : Function.Injective (algebraMap T Q) :=
    tensor_algebraMap_injective_of_comap_surjective (hlocint.comap_surjective hlocinj)
  have : IsScalarTower R T Q := IsScalarTower.to₁₃₄ R Rr T Q
  let j : S →ₐ[R] Q :=
    ((Algebra.TensorProduct.includeRight : Sr →ₐ[Rr] Q).restrictScalars R).comp
      (IsScalarTower.toAlgHom R S Sr)
  let F : T ⊗[R] S →ₐ[T] Q := AlgHom.liftEquiv R T S Q j
  intro a b hab
  apply hQ
  simpa only [F.commutes] using congrArg F hab

theorem tensor_aeval_injective_of_integral_after_away
    {R C K ι : Type*} [CommRing R] [CommRing C] [Field K]
    [Algebra R C] [Algebra R K] (z : ι → C)
    (hz : AlgebraicIndependent R z) (r : R)
    (hr : algebraMap R K r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ,
      IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) :
    Function.Injective (MvPolynomial.aeval
      (fun i => Algebra.TensorProduct.includeRight (A := K) (z i)) :
      MvPolynomial ι K →ₐ[K] K ⊗[R] C) := by
  classical
  let P := MvPolynomial ι R
  let PK := MvPolynomial ι K
  let f : P →ₐ[R] C := MvPolynomial.aeval z
  let : Algebra P C := f.toRingHom.toAlgebra
  have : IsScalarTower R P C :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : Algebra P PK := MvPolynomial.algebraMvPolynomial
  have hPint : ∀ c : C, ∃ n : ℕ, IsIntegral P ((MvPolynomial.C r : P) ^ n • c) := by
    intro c
    obtain ⟨n, p, hpm, hp⟩ := hint c
    let A := Algebra.adjoin R (Set.range z)
    let pC := p.map (algebraMap A C)
    have hL : pC ∈ Polynomial.lifts f.toRingHom := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro m
      dsimp only [pC]
      rw [Polynomial.coeff_map]
      change algebraMap A C (p.coeff m) ∈ Set.range f
      have h := (p.coeff m).2
      have h' := (Algebra.adjoin_range_eq_range_aeval R z).le h
      obtain ⟨q, hq⟩ := (AlgHom.mem_range (MvPolynomial.aeval (R := R) z)).mp h'
      refine ⟨q, ?_⟩
      simpa only [Subalgebra.algebraMap_apply] using hq
    obtain ⟨q, hq, -, hqm⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hL (hpm.map _)
    refine ⟨n, q, hqm, ?_⟩
    have hs : (MvPolynomial.C r : P) ^ n • c = r ^ n • c := by
      simp only [Algebra.smul_def, map_pow]
      change f (MvPolynomial.C r) ^ n * c = algebraMap R C r ^ n * c
      rw [show f (MvPolynomial.C r) = algebraMap R C r from f.commutes r]
    rw [hs]
    change Polynomial.eval₂ f.toRingHom (r ^ n • c) q = 0
    rw [Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_map]
    exact hp
  have hPK : Function.Injective (algebraMap PK (PK ⊗[P] C)) :=
    tensor_algebraMap_injective_of_integral_after_away hz (MvPolynomial.C r)
      (by
        change IsUnit (MvPolynomial.map (algebraMap R K) (MvPolynomial.C r))
        rw [MvPolynomial.map_C]
        exact (isUnit_iff_ne_zero.mpr hr).map MvPolynomial.C) hPint
  let Q := PK ⊗[P] C
  let j : C →ₐ[R] Q :=
    (Algebra.TensorProduct.includeRight : C →ₐ[P] Q).restrictScalars R
  let F : K ⊗[R] C →ₐ[K] Q := AlgHom.liftEquiv R K C Q j
  have hcomp : F.comp (MvPolynomial.aeval
      (fun i => Algebra.TensorProduct.includeRight (A := K) (z i))) =
      (Algebra.TensorProduct.includeLeft : PK →ₐ[K] Q) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X,
      Algebra.TensorProduct.includeRight_apply]
    change F (1 ⊗ₜ[R] z i) = MvPolynomial.X i ⊗ₜ[P] (1 : C)
    rw [AlgHom.liftEquiv_tmul, one_smul]
    have h := (Algebra.TensorProduct.includeRight : C →ₐ[P] Q).commutes
      (MvPolynomial.X i)
    have hX : algebraMap P C (MvPolynomial.X i) = z i := MvPolynomial.aeval_X z i
    have hPX : algebraMap P PK (MvPolynomial.X i) = MvPolynomial.X i :=
      MvPolynomial.map_X (algebraMap R K) i
    rw [hX] at h
    simpa only [j, AlgHom.restrictScalars_apply, Algebra.TensorProduct.algebraMap_apply,
      hPX] using h
  intro a b hab
  apply hPK
  change (Algebra.TensorProduct.includeLeft : PK →ₐ[K] Q) a =
    (Algebra.TensorProduct.includeLeft : PK →ₐ[K] Q) b
  rw [← hcomp]
  exact congrArg F hab

theorem injective_of_integral_comp
    {P D A : Type*} [CommRing P] [Nontrivial P] [CommRing D] [IsDomain D]
    [CommRing A] (i : P →+* D) (j : D →+* A)
    (hi : i.IsIntegral) (hcomp : Function.Injective (j.comp i)) :
    Function.Injective j := by
  let : Algebra P D := i.toAlgebra
  have : Algebra.IsIntegral P D := ⟨hi⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_under_eq_bot (R := P)
  change RingHom.ker (j.comp i) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot (j.comp i)).mp hcomp

theorem adjoinRoot_lift_injective_of_monic
    {P A : Type*} [CommRing P] [Nontrivial P] [CommRing A]
    (F : Polynomial P) (hFm : F.Monic) (hFprime : Prime F)
    (f : P →+* A) (hf : Function.Injective f) (w : A)
    (hw : F.eval₂ f w = 0) :
    Function.Injective (AdjoinRoot.lift f w hw) := by
  have : IsDomain (AdjoinRoot F) := AdjoinRoot.isDomain_of_prime hFprime
  have : Algebra.IsIntegral P (AdjoinRoot F) := AdjoinRoot.isIntegral_of_monic hFm
  apply injective_of_integral_comp (AdjoinRoot.of F) (AdjoinRoot.lift f w hw)
  · exact Algebra.IsIntegral.isIntegral
  · rwa [AdjoinRoot.lift_comp_of]

end Langlands.Algebra.GenericIrreducibilitySpreading
