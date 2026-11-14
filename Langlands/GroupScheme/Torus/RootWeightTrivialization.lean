import Langlands.GroupScheme.Torus.GeometricAdjointWeightRanks
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Simultaneous principal trivialization of actual rank-one weight spaces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Algebra

/-- A finite projective module of rank one at a prime becomes a line on a
principal neighbourhood; its trivialization persists over every algebra
in which the chosen element is invertible. -/
theorem exists_principal_tensorLine_of_rankAtStalk_eq_one
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) (hrank : Module.rankAtStalk M p = 1) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A r) →
        Nonempty (A ⊗[R] M ≃ₗ[A] A) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, hdim⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (Localization.AtPrime p.asIdeal)
  have : Nontrivial (Localization.Away r) :=
    (show Localization.Away r →+* Localization.AtPrime p.asIdeal from
      IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  have hdim' : Module.finrank (Localization.Away r) (LocalizedModule.Away r M) = 1 :=
    hdim.trans hrank
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim'
  let e' : Localization.Away r ⊗[R] M ≃ₗ[Localization.Away r] Localization.Away r :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers r) M).symm.trans e.symm
  refine ⟨r, hr, ?_⟩
  intro A _ _ hu
  let S := Localization.Away r
  let : Algebra S A := (IsLocalization.Away.lift r (g := algebraMap R A) hu).toAlgebra
  have : IsScalarTower R S A :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.Away.lift_eq r hu a).symm
  exact ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A M).symm.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e').trans
      (TensorProduct.AlgebraTensorModule.rid S A A))⟩

/-- Finitely many finite projective modules of rank one at a prime admit
simultaneous trivializations on one principal neighbourhood contained in
any prescribed open neighbourhood. -/
theorem exists_principal_tensorLines_of_rankAtStalk_eq_one
    {R : Type u} [CommRing R] {J : Type v} [Finite J]
    (M : J → Type u) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    [∀ j, Module.Finite R (M j)] [∀ j, Module.Projective R (M j)]
    (p : PrimeSpectrum R) (U : Set (PrimeSpectrum R)) (hU : IsOpen U) (hp : p ∈ U)
    (hrank : ∀ j, Module.rankAtStalk (M j) p = 1) :
    ∃ r : R, r ∉ p.asIdeal ∧ (PrimeSpectrum.basicOpen r : Set _) ⊆ U ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A r) →
        ∀ j, Nonempty (A ⊗[R] M j ≃ₗ[A] A) := by
  classical
  let := Fintype.ofFinite J
  choose f hf he using fun j =>
    exists_principal_tensorLine_of_rankAtStalk_eq_one p (hrank j)
  obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
  let r := a * ∏ j, f j
  have hprod : (∏ j, f j) ∉ p.asIdeal := by
    change (∏ j, f j) ∈ p.asIdeal.primeCompl
    exact p.asIdeal.primeCompl.prod_mem (fun j _ => hf j)
  refine ⟨r, p.isPrime.mul_notMem ha hprod, ?_, ?_⟩
  · exact (SetLike.coe_subset_coe.mpr (PrimeSpectrum.basicOpen_mul_le_left a _)).trans hsub
  · intro A _ _ hu j
    apply he j A
    apply isUnit_of_dvd_unit (map_dvd (algebraMap R A) ?_) hu
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem f (Finset.mem_univ j)) a

end Langlands.Algebra

namespace Langlands.GroupScheme.splitTorus

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- A trivialization of an actual exponent weight space as a free line. -/
abbrev ExponentWeightLineTrivialization (m : I → ℤ) :=
  exponentWeightSpace I G i m ≃ₗ[R] R

local instance affine_principalBaseChange (r : R) :
    IsAffineHom ((baseChange (algebraBaseMap R (Localization.Away r))).obj G).X.hom :=
  inferInstanceAs (IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap R (Localization.Away r))))

/-- Every finite family of actual exponent weight spaces of rank one at a
point is free of rank one after one principal localization inside any
prescribed open neighbourhood of the point. -/
theorem exists_principal_exponentWeightLines
    {J : Type v} [Finite J] (m : J → (I → ℤ))
    (p : PrimeSpectrum R) (U : Set (PrimeSpectrum R)) (hU : IsOpen U) (hp : p ∈ U)
    (hrank : ∀ j, exponentWeightRank I G i (m j) p = 1) :
    ∃ r : R, r ∉ p.asIdeal ∧ (PrimeSpectrum.basicOpen r : Set _) ⊆ U ∧
      ∀ j, Nonempty
        (ExponentWeightLineTrivialization I
          ((baseChange (algebraBaseMap R (Localization.Away r))).obj G)
          (baseChangeHom (K := Localization.Away r) G I i) (m j)) := by
  obtain ⟨r, hr, hsub, he⟩ :=
    Langlands.Algebra.exists_principal_tensorLines_of_rankAtStalk_eq_one
      (fun j => exponentWeightSpace I G i (m j)) p U hU hp hrank
  refine ⟨r, hr, hsub, fun j => ?_⟩
  obtain ⟨e⟩ := he (Localization.Away r) (IsLocalization.Away.algebraMap_isUnit r) j
  exact ⟨(exponentWeightBaseChangeEquiv (K := Localization.Away r) G I i (m j)).symm.trans e⟩

end Langlands.GroupScheme.splitTorus
