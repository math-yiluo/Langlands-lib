import Langlands.Algebra.EssFinitePresentationTowerCancellationProof
import Langlands.Algebra.EssFinitePresentationTransportProof
import Langlands.CommutativeAlgebra.EtaleFlatLocalDescentProof
import Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
import Langlands.RingTheory.Smooth.SectionJetIsomorphismLocus

/-! # Étaleness from isomorphisms on section jets -/

namespace Algebra.SectionJet

open Langlands.CommutativeAlgebra

universe u v w

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [CommRing A]
  [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
  (ε : A →ₐ[R] R)

local notation "φ" => IsScalarTower.toAlgHom R P A
local notation "δP" => ε.comp φ
local notation "IA" => RingHom.ker ε
local notation "IP" => RingHom.ker δP

private noncomputable def truncationEquiv
    (h : ∀ n : ℕ, Function.Bijective (jetMap (ε := ε) (f := φ) rfl n)) (k : ℕ) :
    (P ⧸ IP ^ k) ≃ₐ[R] A ⧸ IA ^ k :=
  AlgEquiv.ofBijective (Ideal.quotientMapₐ _ φ (ker_pow_le_comap (ε := ε) (f := φ) rfl k)) (by
    cases k with
    | zero =>
      have : Subsingleton (P ⧸ IP ^ (0 : ℕ)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      have : Subsingleton (A ⧸ IA ^ (0 : ℕ)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ a⟩⟩
    | succ n => exact h n)

private noncomputable def completionEquiv
    (h : ∀ n : ℕ, Function.Bijective (jetMap (ε := ε) (f := φ) rfl n)) :
    AdicCompletion IP P ≃ₐ[P] AdicCompletion IA A := by
  have he {a b : ℕ} (hab : a ≤ b) (x : P ⧸ IP ^ b) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (truncationEquiv ε h b x) =
        truncationEquiv ε h a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let e := FormallySmoothLocalCompletion.adicCompletionAlgEquiv IP IA (truncationEquiv ε h) he
  refine { e.toRingEquiv with commutes' := fun p => ?_ }
  change e (AdicCompletion.of IP P p) = AdicCompletion.of IA A (φ p)
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [e, FormallySmoothLocalCompletion.adicCompletionAlgEquiv,
    AlgEquiv.ofAlgHom_apply]
  rw [AdicCompletion.evalₐ_liftAlgHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AdicCompletion.evalₐ_of]
  · rfl
  · intro a b hab
    refine AlgHom.ext fun x => ?_
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.factorₐ_apply]
    rw [← FormallySmoothLocalCompletion.factor_evalₐ IP hab x]
    exact he hab _

private theorem flat_at_section [IsNoetherianRing P] [IsNoetherianRing A]
    (h : ∀ n : ℕ, Function.Bijective (jetMap (ε := ε) (f := φ) rfl n))
    (s : Ideal R) [s.IsPrime] :
    Module.Flat P (Localization.AtPrime (s.comap ε.toRingHom)) := by
  let C := AdicCompletion IA A
  let q := s.comap ε.toRingHom
  have hε : Function.Surjective ε := fun x => ⟨algebraMap R A x, ε.commutes x⟩
  let Q := s.comap (AdicCompletion.kerProj hε).toRingHom
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : q = Q.comap (algebraMap A C) := rfl
  have : Q.LiesOver q := ⟨hQ⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  have : Module.Flat P C :=
    Module.Flat.of_linearEquiv (completionEquiv ε h).symm.toLinearEquiv
  have : Module.Flat P (Localization.AtPrime Q) :=
    Module.Flat.trans P C (Localization.AtPrime Q)
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q) := by
    apply RingHom.flat_algebraMap_iff.mp
    have hflat : (algebraMap A C).Flat :=
      RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian (I := IA))
    exact hflat.localRingHom Q q hQ
  have : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_flat_of_faithfullyFlat P (Localization.AtPrime q) (Localization.AtPrime Q)

private theorem map_sectionPrime_eq_maximalIdeal [IsNoetherianRing A]
    (h : Function.Surjective (jetMap (ε := ε) (f := φ) rfl 1))
    (s : Ideal R) [s.IsPrime] :
    let q := s.comap ε.toRingHom
    (q.under P).map (algebraMap P (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  let q := s.comap ε.toRingHom
  let p := q.under P
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime q)
  change p.map (algebraMap P (Localization.AtPrime q)) = m
  have hI : IA ≤ q := Ideal.ker_le_comap ε.toRingHom
  have hq : q ≤ p.map (algebraMap P A) ⊔ q ^ 2 := by
    intro a ha
    obtain ⟨b, hb⟩ := h (Ideal.Quotient.mk _ a)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : Ideal.Quotient.mk (IA ^ 2) (φ b) = Ideal.Quotient.mk (IA ^ 2) a := hb
    have hab : a - φ b ∈ IA ^ 2 := Ideal.Quotient.eq.mp hb'.symm
    have hp : b ∈ p := by
      change φ b ∈ q
      simpa only [sub_sub_cancel] using sub_mem ha (hI (Ideal.pow_le_self two_ne_zero hab))
    exact sub_add_cancel a (φ b) ▸ add_mem
      (Ideal.mem_sup_right ((Ideal.pow_right_mono hI 2) hab))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem (algebraMap P A) hp))
  have hl := Ideal.map_mono (f := algebraMap A (Localization.AtPrime q)) hq
  rw [Ideal.map_sup, Ideal.map_map, ← IsScalarTower.algebraMap_eq P A,
    Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal] at hl
  apply le_antisymm
  · rw [show m = q.map (algebraMap A (Localization.AtPrime q)) from
      (Localization.AtPrime.map_eq_maximalIdeal (I := q)).symm,
      IsScalarTower.algebraMap_eq P A, ← Ideal.map_map]
    exact Ideal.map_mono Ideal.map_comap_le
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    rwa [Ideal.smul_eq_mul, ← pow_two]

private theorem sectionResidueField_separable (s : Ideal R) [s.IsPrime] :
    let q := s.comap ε.toRingHom
    let p := q.under P
    let := Localization.AtPrime.algebraOfLiesOver p q
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  let q := s.comap ε.toRingHom
  let p := q.under P
  let := Localization.AtPrime.algebraOfLiesOver p q
  change Algebra.IsSeparable p.ResidueField q.ResidueField
  let g := Ideal.ResidueField.map q s ε.toRingHom rfl
  let k := Ideal.ResidueField.map p s (δP).toRingHom rfl
  have hδ : Function.Surjective (δP).toRingHom :=
    fun x => ⟨algebraMap R P x, (δP).commutes x⟩
  have hk : Function.Surjective k :=
    ((RingHom.surjectiveOnStalks_of_surjective hδ).residueFieldMap_bijective p s rfl).2
  have hcomp : g.comp (algebraMap p.ResidueField q.ResidueField) = k := by
    apply Ideal.ResidueField.ringHom_ext
    refine RingHom.ext fun x => ?_
    change g (Ideal.ResidueField.map p q (algebraMap P A) rfl
      (algebraMap P p.ResidueField x)) = k (algebraMap P p.ResidueField x)
    simp [g, k, AlgHom.comp_apply]
  constructor
  intro y
  obtain ⟨x, hx⟩ := hk (g y)
  have hxy : algebraMap p.ResidueField q.ResidueField x = y :=
    g.injective ((DFunLike.congr_fun hcomp x).trans hx)
  exact hxy ▸ isSeparable_algebraMap x

/-- A finitely presented map of augmented algebras over a noetherian source ring
is étale at the section if all of its actual section jets are isomorphisms. -/
def SectionJetEtaleStatement : Prop :=
  ∀ (R : Type u) (P : Type v) (A : Type w)
    [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    [IsNoetherianRing P] [FinitePresentation P A] (ε : A →ₐ[R] R),
    (∀ n : ℕ, Function.Bijective
      (jetMap (δ := ε.comp (IsScalarTower.toAlgHom R P A)) rfl n)) →
    ∀ (s : Ideal R) [s.IsPrime], IsEtaleAt P (s.comap ε.toRingHom)

theorem sectionJetEtale : SectionJetEtaleStatement.{u, v, w} := by
  intro R P A _ _ _ _ _ _ _ _ _ ε h s _
  let q := s.comap ε.toRingHom
  let p := q.under P
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing P A
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).mpr (flat_at_section ε h s)
  have : IsUnramifiedAt P q := (isUnramifiedAt_iff_map_eq P p q).mpr
    ⟨sectionResidueField_separable (P := P) ε s,
      map_sectionPrime_eq_maximalIdeal ε (h 1).2 s⟩
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    FormallyUnramified.of_restrictScalars P _ _
  have hp := Langlands.Algebra.essFinitePresentation_of_isLocalization P P
    (Localization.AtPrime p) p.primeCompl
  have hq := Langlands.Algebra.essFinitePresentation_of_isLocalization P A
    (Localization.AtPrime q) q.primeCompl
  have hlocal := Langlands.Algebra.essFinitePresentationTowerCancellation P
    (Localization.AtPrime p) (Localization.AtPrime q) hp hq
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation _ _ hlocal
  have : FormallyEtale P (Localization.AtPrime p) := FormallyEtale.of_isLocalization p.primeCompl
  exact FormallyEtale.comp P (Localization.AtPrime p) (Localization.AtPrime q)

end Algebra.SectionJet
