import Langlands.RingTheory.Smooth.SectionJetEtale
import Mathlib.RingTheory.Localization.BaseChange

/-! # Smooth neighborhoods from isomorphisms on section jets -/

noncomputable section

universe u v w t

open scoped TensorProduct

namespace Algebra.SectionJet

open PrimeSpectrum

/-- An affine finitely presented augmented algebra smooth at every point of the
section has a smooth principal neighborhood defined by an element of augmentation one. -/
theorem exists_smooth_away_of_section {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (ε : A →ₐ[R] R)
    (hs : ∀ (s : Ideal R) [s.IsPrime], IsSmoothAt R (s.comap ε.toRingHom)) :
    ∃ a : A, ε a = 1 ∧ Smooth R (Localization.Away a) := by
  obtain ⟨J, hJ⟩ := (isClosed_iff_zeroLocus_ideal _).mp
    (isOpen_smoothLocus (R := R) (A := A)).isClosed_compl
  have htop : J.map ε.toRingHom = ⊤ := by
    by_contra h
    obtain ⟨s, hsmax, hle⟩ := Ideal.exists_le_maximal _ h
    have : s.IsPrime := hsmax.isPrime
    have hh : comap ε.toRingHom ⟨s, inferInstance⟩ ∈ smoothLocus R A := hs s
    have hm : comap ε.toRingHom ⟨s, inferInstance⟩ ∈ zeroLocus (J : Set A) :=
      (mem_zeroLocus _ _).mpr (Ideal.map_le_iff_le_comap.mp hle)
    rw [← hJ] at hm
    exact hm hh
  have hsurj : Function.Surjective ε.toRingHom := fun r => ⟨algebraMap R A r, ε.commutes r⟩
  have hone : (1 : R) ∈ J.map ε.toRingHom := by rw [htop]; trivial
  obtain ⟨a, haJ, ha⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hone
  refine ⟨a, ha, basicOpen_subset_smoothLocus_iff_smooth.mp ?_⟩
  intro q hq
  by_contra h
  have hzero : q ∈ zeroLocus (J : Set A) := by
    rw [← hJ]
    exact (Set.mem_compl_iff _ _).mpr h
  exact ((mem_basicOpen a q).mp hq) ((mem_zeroLocus _ _).mp hzero haJ)

variable {R : Type u} {P : Type v} {A : Type w}
    [CommRing R] [CommRing P] [CommRing A] [Algebra R P] [Algebra R A]
    {δ : P →ₐ[R] R} {ε : A →ₐ[R] R} {f : P →ₐ[R] A} (hf : ε.comp f = δ)

private theorem smooth_along_section_of_bijective [IsNoetherianRing R]
    [Smooth R P] [FinitePresentation R A]
    (h : ∀ n : ℕ, Function.Bijective (jetMap hf n))
    (s : Ideal R) [s.IsPrime] : IsSmoothAt R (s.comap ε.toRingHom) := by
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsNoetherianRing P := FiniteType.isNoetherianRing R P
  have : FinitePresentation P A := FinitePresentation.of_restrict_scalars_finitePresentation R P A
  subst δ
  have : IsEtaleAt P (s.comap ε.toRingHom) := sectionJetEtale R P A ε h s
  exact FormallySmooth.comp R P (Localization.AtPrime (s.comap ε.toRingHom))

/-- Killing the coefficient ideal of the surjective maps of section jets gives a
smooth principal neighborhood of the entire section on the test algebra. -/
def SectionJetSmoothNeighborhoodStatement : Prop :=
  ∀ (R : Type u) (P : Type v) (A : Type w) (B : Type t)
    [CommRing R] [CommRing P] [CommRing A] [CommRing B]
    [Algebra R P] [Algebra R A] [Algebra R B]
    [IsNoetherianRing R] [Smooth R P] [FinitePresentation R A]
    (δ : P →ₐ[R] R) (ε : A →ₐ[R] R) (f : P →ₐ[R] A) (hf : ε.comp f = δ),
    (∀ n : ℕ, Function.Surjective (jetMap hf n)) →
    jetIsomorphismIdeal hf ≤ RingHom.ker (algebraMap R B) →
    ∃ a : B ⊗[R] A, baseChangeAugmentation ε B a = 1 ∧ Smooth B (Localization.Away a)

theorem sectionJetSmoothNeighborhood : SectionJetSmoothNeighborhoodStatement.{u, v, w, t} := by
  intro R P A B _ _ _ _ _ _ _ _ _ _ δ ε f hf hsurj ht
  let J := jetIsomorphismIdeal hf
  let C := R ⧸ J
  have hC : J ≤ RingHom.ker (algebraMap R C) := fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hj := (sectionJetIsomorphismLocus R P A C δ ε f hf hsurj).mp hC
  obtain ⟨a, ha, hsm⟩ := exists_smooth_away_of_section (baseChangeAugmentation ε C) <|
    smooth_along_section_of_bijective (baseChangeAugmentation_comp_map hf C) hj
  let φ : C →+* B := Ideal.Quotient.lift J (algebraMap R B) fun _ hr => ht hr
  let := φ.toAlgebra
  have hR : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq' rfl
  let e := Algebra.TensorProduct.cancelBaseChange R C B B A
  let b := (1 : B) ⊗ₜ[C] a
  have hεe : (baseChangeAugmentation ε B).comp e.toAlgHom =
      baseChangeAugmentation (baseChangeAugmentation ε C) B := by
    apply Algebra.TensorProduct.ext'
    intro x y
    induction y using TensorProduct.inductionOn with
    | tmul c d =>
      simp [e, Algebra.smul_def, IsScalarTower.algebraMap_apply R C B, mul_left_comm, mul_comm]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  refine ⟨e b, ?_, ?_⟩
  · change ((baseChangeAugmentation ε B).comp e.toAlgHom) b = 1
    rw [hεe]
    simp [b, ha]
  · have hsm' : Smooth B (B ⊗[C] Localization.Away a) := inferInstance
    have hsmb : Smooth B (Localization.Away b) :=
      Smooth.of_equiv (IsLocalization.Away.tensorProductEquivTMulRight C B a (Localization.Away a))
    exact Smooth.of_equiv (IsLocalization.algEquivOfAlgEquiv
      (Localization.Away b) (Localization.Away (e b)) e (Submonoid.map_powers e b))

end Algebra.SectionJet
