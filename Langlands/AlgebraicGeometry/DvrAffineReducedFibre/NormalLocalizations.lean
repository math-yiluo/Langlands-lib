import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.TotalFractions
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Normal localizations of a reduced Noetherian ring's normalization -/

open Polynomial TensorProduct

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private theorem nonZeroDivisor_of_notMem_minimalPrimes {A : Type u} [CommRing A] [IsReduced A]
    {a : A} (ha : ∀ q ∈ minimalPrimes A, a ∉ q) :
    a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_left]
  intro b hb
  have hn : b ∈ nilradical A := by
    change b ∈ (⊥ : Ideal A).radical
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro q hq
    exact (hq.isPrime.mem_or_mem (hb ▸ q.zero_mem)).resolve_left (ha q hq)
  exact (mem_nilradical.mp hn).eq_zero

private theorem under_mem_minimalPrimes_fractionRing (A : Type u) [CommRing A]
    [IsReduced A] [IsNoetherianRing A] (q : Ideal (FractionRing A)) [q.IsPrime] :
    q.under A ∈ minimalPrimes A := by
  let M := nonZeroDivisors A
  let K := FractionRing A
  have hd : Disjoint (M : Set A) (q.under A) :=
    (IsLocalization.disjoint_under_iff M K q).mpr Ideal.IsPrime.ne_top'
  have hsub : (q.under A : Set A) ⊆ ⋃ p ∈ minimalPrimes A, (p : Set A) := by
    intro a haq
    by_contra h
    have ha : a ∈ M := nonZeroDivisor_of_notMem_minimalPrimes fun p hp hap =>
      h (Set.mem_iUnion₂.mpr ⟨p, hp, hap⟩)
    exact Set.disjoint_left.mp hd ha haq
  obtain ⟨p, hp, hle⟩ :=
    (Ideal.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing A)
      (f := id) ⊥ ⊥ (fun _ hp _ _ => hp.isPrime)).mp hsub
  have heq : q.under A = p :=
    le_antisymm hle (hp.2 ⟨inferInstance, bot_le⟩ hle)
  simpa only [heq] using hp

/-- The total ring of fractions of a reduced Noetherian ring is Artinian. -/
theorem isArtinianRing_fractionRing (A : Type u) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] : IsArtinianRing (FractionRing A) := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  apply Ring.krullDimLE_zero_iff.mpr
  intro q hq
  obtain ⟨p, hp, hle⟩ := q.exists_le_maximal hq.ne_top
  have hq₀ := under_mem_minimalPrimes_fractionRing A q
  have hp₀ := under_mem_minimalPrimes_fractionRing A p
  have hle₀ : q.under A ≤ p.under A := Ideal.comap_mono hle
  have hEq : q.under A = p.under A := le_antisymm hle₀ (hp₀.2 hq₀.1 hle₀)
  have hqp : q = p :=
    (IsLocalization.orderEmbedding (nonZeroDivisors A) (FractionRing A)).injective hEq
  exact hqp ▸ hp

private theorem isIntegral_pi_of_finite {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    {x : ∀ i, B i} (hx : ∀ i, IsIntegral R (x i)) : IsIntegral R x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose P hP hroot using hx
  refine ⟨∏ i, P i, monic_prod_of_monic _ _ (fun i _ => hP i), funext fun i => ?_⟩
  change (Pi.evalRingHom B i) (eval₂ (algebraMap R (∀ i, B i)) x (∏ j, P j)) = 0
  rw [hom_eval₂]
  change (eval₂RingHom (algebraMap R (B i)) (x i)) (∏ j, P j) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hroot i)

/-- Integral closure in a reduced Artinian algebra is the product of the integral
closures in the fields given by its maximal-ideal quotients. -/
def integralClosureEquivArtinianComponents (A K : Type u) [CommRing A] [CommRing K]
    [Algebra A K] [IsReduced K] [IsArtinianRing K] :
    integralClosure A K ≃ₐ[A]
      (∀ m : MaximalSpectrum K, integralClosure A (K ⧸ m.asIdeal)) := by
  let e := (IsArtinianRing.equivPi K).restrictScalars A
  let f : integralClosure A K →ₐ[A]
      (∀ m : MaximalSpectrum K, integralClosure A (K ⧸ m.asIdeal)) :=
    { toFun := fun x m => ⟨e x.val m, x.property.map
        ((Pi.evalAlgHom A (fun m : MaximalSpectrum K => K ⧸ m.asIdeal) m).comp e.toAlgHom)⟩
      map_one' := by ext m; exact congrFun (map_one e) m
      map_mul' := fun x y => by ext m; exact congrFun (map_mul e x.val y.val) m
      map_zero' := by ext m; exact congrFun (map_zero e) m
      map_add' := fun x y => by ext m; exact congrFun (map_add e x.val y.val) m
      commutes' := fun a => by ext m; exact congrFun (e.commutes a) m }
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact e.injective (funext fun m => congrArg (fun t => (t m).val) h)
  · intro y
    let x := e.symm (fun m => (y m).val)
    have hx : IsIntegral A x :=
      (isIntegral_pi_of_finite (fun m => (y m).property)).map e.symm
    exact ⟨⟨x, hx⟩, funext fun m =>
      Subtype.ext (congrFun (e.apply_symm_apply (fun m => (y m).val)) m)⟩

private theorem normal_localizations_of_algEquiv_pi {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type v} [Finite ι] {C : ι → Type u}
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    [∀ i, IsDomain (C i)] [∀ i, IsIntegrallyClosed (C i)]
    (e : B ≃ₐ[A] ∀ i, C i) (p : Ideal B) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let q : PrimeSpectrum (∀ i, C i) := PrimeSpectrum.comap e.symm.toRingHom ⟨p, inferInstance⟩
  obtain ⟨i, r, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq q
  have heq : p = (r.asIdeal.comap (Pi.evalRingHom C i)).comap e.toRingHom := by
    rw [show r.asIdeal.comap (Pi.evalRingHom C i) = q.asIdeal from congrArg PrimeSpectrum.asIdeal hq]
    ext a
    change a ∈ p ↔ e.symm (e a) ∈ p
    rw [e.symm_apply_apply]
  let eloc := Localization.localRingEquiv p (r.asIdeal.comap (Pi.evalRingHom C i)) e.toRingEquiv heq
  let ecomp := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom r.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective r.asIdeal)
  let e' := eloc.trans ecomp
  have hClosed : IsIntegrallyClosed (Localization.AtPrime r.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ _ r.asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨e'.toMulEquiv.isDomain, hClosed.of_equiv e'.symm⟩

/-- The normalization in total fractions of a reduced Noetherian ring has
integrally closed domain localizations at all prime ideals. -/
theorem normal_localizations_totalNormalization (A : Type u) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] (p : Ideal (integralClosure A (FractionRing A))) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let K := FractionRing A
  have : IsReduced K := isReduced_localizationPreserves (nonZeroDivisors A) K inferInstance
  have : IsArtinianRing K := isArtinianRing_fractionRing A
  let B (m : MaximalSpectrum K) := integralClosure A (K ⧸ m.asIdeal)
  have (m : MaximalSpectrum K) : IsDomain (B m) := inferInstance
  have (m : MaximalSpectrum K) : IsIntegrallyClosed (B m) := by
    let : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field _
    exact IsIntegrallyClosed.of_isIntegrallyClosedIn (B m) (K ⧸ m.asIdeal)
  exact normal_localizations_of_algEquiv_pi (integralClosureEquivArtinianComponents A K) p

/-- The integral closure of a flat finite-type algebra in its smooth generic
fibre has integrally closed domain localizations at all prime ideals. -/
theorem normal_localizations_genericNormalization (R A : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FiniteType R A]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]
    (p : Ideal (integralClosure A (A ⊗[R] FractionRing R))) [p.IsPrime] :
    letI : CommRing (Localization.AtPrime p) :=
      OreLocalization.instCommRing (R := ↥(integralClosure A (A ⊗[R] FractionRing R)))
        (S := p.primeCompl)
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let : CommRing (Localization.AtPrime p) :=
    OreLocalization.instCommRing (R := ↥(integralClosure A (A ⊗[R] FractionRing R)))
      (S := p.primeCompl)
  let K := FractionRing R
  let G := A ⊗[R] K
  have : IsReduced (K ⊗[R] A) := SmoothReducedProof.isReduced_of_smooth_of_domain K (K ⊗[R] A)
  have : IsReduced G := isReduced_of_injective (Algebra.TensorProduct.comm R A K).toRingHom
    (Algebra.TensorProduct.comm R A K).injective
  let f := genericFibreTotalFractionsMap R A
  have hAG : Function.Injective (algebraMap A G) := by
    intro a b h
    apply IsFractionRing.injective A (FractionRing A)
    rw [← f.commutes a, ← f.commutes b, h]
  have : IsReduced A := isReduced_of_injective (algebraMap A G) hAG
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : IsIntegrallyClosed G := isIntegrallyClosed_genericFibre R A
  let e := integralClosureGenericFibreEquivTotalFractions R A
  let q := p.comap e.symm.toRingHom
  have hq : q.IsPrime := Ideal.IsPrime.comap _
  have hEq : p = q.comap e.toRingHom := by
    ext a
    change a ∈ p ↔ e.symm (e a) ∈ p
    rw [e.symm_apply_apply]
  obtain ⟨_, hClosed⟩ := normal_localizations_totalNormalization A q
  let loc := Localization.localRingEquiv p q e.toRingEquiv hEq
  exact ⟨loc.toMulEquiv.isDomain, hClosed.of_equiv loc.symm⟩

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
