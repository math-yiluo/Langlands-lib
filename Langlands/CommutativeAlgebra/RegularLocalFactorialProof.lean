import Langlands.CommutativeAlgebra.RegularLocalFactorialStatement
import Langlands.CommutativeAlgebra.RegularLocalFactorialTools
import Langlands.CommutativeAlgebra.RegularLocalLocalizationsProof
import Langlands.CommutativeAlgebra.RegularLocalAwayPicardProof
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Factoriality of regular local rings -/

universe u

open TensorProduct IsLocalRing

namespace Langlands.CommutativeAlgebra.RegularLocalFactorial

variable {R : Type u} [CommRing R]

/-- An ideal-valued rank-one identity for every linear functional on an ideal. -/
theorem ideal_dual_smul (I : Ideal R) (f : Module.Dual R I) (x y : I) :
    f x • y = f y • x := by
  apply Subtype.ext
  have h : (x : R) • y = (y : R) • x := by
    apply Subtype.ext
    exact mul_comm _ _
  have h' := congrArg f h
  change f x * (y : R) = f y * (x : R)
  simpa only [map_smul, smul_eq_mul, mul_comm] using h'.symm

/-- On an ideal, the tensor-to-endomorphism map acts by its contraction scalar. -/
theorem ideal_dualTensorHom_apply (I : Ideal R) (t : Module.Dual R I ⊗[R] I) (x : I) :
    dualTensorHom R I I t x = contractLeft R I t • x := by
  induction t using TensorProduct.inductionOn with
  | tmul f y =>
    simpa only [dualTensorHom_apply, contractLeft_apply] using ideal_dual_smul I f x y
  | add t s ht hs => simp [ht, hs, add_smul]

/-- A nonzero finite projective ideal in a domain is an invertible module. -/
theorem moduleInvertible_of_projective_ideal [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    [Module.Finite R I] [Module.Projective R I] : Module.Invertible R I := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let x : I := ⟨a, ha⟩
  have hc := dualTensorHom_bijective (R := R) (M := I) (N := I)
  refine ⟨⟨?_, ?_⟩⟩
  · intro t s hts
    apply hc.1
    ext y
    simp only [ideal_dualTensorHom_apply, hts]
  · obtain ⟨t, ht⟩ := hc.2 (LinearMap.id : I →ₗ[R] I)
    have htx : contractLeft R I t = 1 := by
      have heq := congrArg (fun f : I →ₗ[R] I => (f x : R)) ht
      rw [ideal_dualTensorHom_apply] at heq
      change contractLeft R I t * a = a at heq
      exact (mul_right_cancel₀ ha0 (heq.trans (one_mul a).symm))
    intro r
    exact ⟨r • t, by simp [htx]⟩

/-- A finite projective ideal over a domain with trivial Picard group is principal. -/
theorem isPrincipal_of_projective_of_picard_trivial [IsDomain R]
    [Subsingleton (CommRing.Pic R)] (I : Ideal R)
    [Module.Finite R I] [Module.Projective R I] : I.IsPrincipal := by
  by_cases hI : I = ⊥
  · rw [hI]; infer_instance
  · have := moduleInvertible_of_projective_ideal I hI
    have : Module.Free R I := inferInstance
    obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp this
    exact ⟨(e.symm 1 : R), Submodule.eq_span_singleton_of_surjective e.symm.surjective⟩

/-- A principal ideal in a domain is projective, including the zero ideal. -/
theorem moduleProjective_of_isPrincipal_ideal [IsDomain R] (I : Ideal R)
    (hI : I.IsPrincipal) : Module.Projective R I := by
  obtain ⟨a, ha⟩ := hI.principal
  change I = Ideal.span {a} at ha
  subst I
  by_cases ha0 : a = 0
  · subst a
    have : Module.Free R (Ideal.span ({0} : Set R)) :=
      Module.Free.of_equiv (LinearEquiv.ofEq (⊥ : Submodule R R) _
        Ideal.span_singleton_zero.symm)
    infer_instance
  · have : Module.Free R (Ideal.span {a}) :=
      Module.Free.of_equiv (LinearEquiv.toSpanNonzeroSingleton R R a ha0)
    infer_instance

/-- A finitely presented ideal whose maximal stalks are principal is projective. -/
theorem moduleProjective_of_local_principal [IsDomain R] (I : Ideal R)
    [Module.FinitePresentation R I]
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime P))).IsPrincipal) :
    Module.Projective R I := by
  apply Module.projective_of_localization_maximal'
    (Rₚ := fun P _ => Localization.AtPrime P)
    (Mₚ := fun P _ => I.localized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap R (Localization.AtPrime P)))
    (fun P _ => I.toLocalized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap R (Localization.AtPrime P)))
  intro P hP
  have heq : I.localized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap R (Localization.AtPrime P)) =
      I.map (algebraMap R (Localization.AtPrime P)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [heq]
  exact moduleProjective_of_isPrincipal_ideal _ (H P)

/-- Local principality and a trivial Picard group give a global generator. -/
theorem isPrincipal_of_local_principal_of_picard_trivial [IsDomain R]
    [IsNoetherianRing R] [Subsingleton (CommRing.Pic R)] (I : Ideal R)
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime P))).IsPrincipal) :
    I.IsPrincipal := by
  have : Module.FinitePresentation R I := Module.finitePresentation_of_finite R I
  have := moduleProjective_of_local_principal I H
  exact isPrincipal_of_projective_of_picard_trivial I

/-- A Noetherian domain with factorial stalks and trivial Picard group is factorial. -/
theorem uniqueFactorizationMonoid_of_local_of_picard_trivial [IsDomain R]
    [IsNoetherianRing R] [Subsingleton (CommRing.Pic R)]
    (H : ∀ (P : Ideal R) [P.IsMaximal], UniqueFactorizationMonoid (Localization.AtPrime P)) :
    UniqueFactorizationMonoid R := by
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro I hI hI1
  apply isPrincipal_of_local_principal_of_picard_trivial I
  intro P hP
  by_cases hIP : I ≤ P
  · have := H P
    have := Ideal.isPrime_map_of_isLocalizationAtPrime P
      (S := Localization.AtPrime P) hIP
    apply UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    rw [← IsLocalization.height_under P.primeCompl,
      Ideal.under_map_of_isLocalizationAtPrime P hIP, hI1]
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hIP]
    infer_instance

/-- Dimension induction from localization regularity and Picard vanishing. -/
theorem uniqueFactorizationMonoid_of_spanFinrank_eq
    (Hreg : ∀ (A : Type u) [CommRing A], IsRegularLocalRing A → IsRegularRing A)
    (Hpic : ∀ (A : Type u) [CommRing A], IsRegularLocalRing A →
      ∀ x : A, Subsingleton (CommRing.Pic (Localization.Away x)))
    (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → UniqueFactorizationMonoid R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    have := regularLocalDomain R inferInstance
    by_cases hn1 : n ≤ 1
    · have := isPrincipalIdealRing_of_spanFinrank_le_one (R := R) (hn ▸ hn1)
      infer_instance
    · obtain ⟨x, hxm, hx2, hxp⟩ := exists_prime_parameter (R := R) (by omega)
      have : IsDomain (Localization.Away x) := IsLocalization.Away.isDomain _ hxp.ne_zero
      have := Hpic R inferInstance x
      apply (UniqueFactorizationMonoid.iff_localizationAway_of_prime hxp).mpr
      apply uniqueFactorizationMonoid_of_local_of_picard_trivial
      intro P hP
      let q : Ideal R := P.under R
      have hq : q.IsPrime := inferInstance
      have hxnq : x ∉ q := by
        intro hxq
        exact hP.ne_top (P.eq_top_of_isUnit_mem hxq
          (IsLocalization.Away.algebraMap_isUnit x))
      have hq_lt : q < maximalIdeal R :=
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hq.ne_top) (by
          intro heq
          exact hxnq (heq ▸ hxm))
      have hheight : q.height < (maximalIdeal R).height :=
        Ideal.height_strict_mono_of_isPrime hq_lt
      have := Hreg R inferInstance
      have hdim : (maximalIdeal (Localization.AtPrime q)).spanFinrank <
          (maximalIdeal R).spanFinrank := by
        have hdim' :
            ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞) <
            ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
          rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
            IsRegularLocalRing.spanFinrank_maximalIdeal,
            IsLocalization.AtPrime.ringKrullDim_eq_height q,
            ← maximalIdeal_height_eq_ringKrullDim]
          exact_mod_cast hheight
        exact_mod_cast hdim'
      have := ih (maximalIdeal (Localization.AtPrime q)).spanFinrank (by omega)
        (Localization.AtPrime q) rfl
      exact (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers x) P).toRingEquiv.toMulEquiv.uniqueFactorizationMonoid this

/-- Conditional assembly of the target from localization regularity and Picard vanishing. -/
theorem regularLocalFactorial_of_localizations_of_awayPicard
    (Hreg : ∀ (A : Type u) [CommRing A], IsRegularLocalRing A → IsRegularRing A)
    (Hpic : ∀ (A : Type u) [CommRing A], IsRegularLocalRing A →
      ∀ x : A, Subsingleton (CommRing.Pic (Localization.Away x))) :
    RegularLocalFactorialStatement.{u} := by
  intro R _ hR
  exact uniqueFactorizationMonoid_of_spanFinrank_eq Hreg Hpic _ R rfl

end Langlands.CommutativeAlgebra.RegularLocalFactorial

namespace Langlands.CommutativeAlgebra

/-- Every regular local ring is a unique factorization domain (Stacks Project, Tag 0AG0). -/
theorem regularLocalFactorial : RegularLocalFactorialStatement.{u} :=
  RegularLocalFactorial.regularLocalFactorial_of_localizations_of_awayPicard
    regularLocalLocalizations regularLocalAwayPicard

end Langlands.CommutativeAlgebra
