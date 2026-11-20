import Langlands.RingTheory.Smooth.AugmentationCotangentDifferentials
import Langlands.RingTheory.Smooth.SectionJetConormalBaseChange
import Langlands.RingTheory.Smooth.SectionJetSmoothNeighborhood
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # A closed smooth-section locus on a chart with conormal generators -/

noncomputable section

open scoped TensorProduct

namespace Algebra.SectionJet

open Langlands.GroupScheme.CoordinateWeights

/-- Formal smoothness of the localization at each section prime, with
a prescribed conormal dimension over each residue field of the base. -/
def SmoothAlongSectionOfRank {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (r : ℕ) : Prop :=
  (∀ (s : Ideal R) [s.IsPrime], IsSmoothAt R (s.comap ε.toRingHom)) ∧
    ∀ s : PrimeSpectrum R,
      Module.finrank s.asIdeal.ResidueField (s.asIdeal.Fiber (RingHom.ker ε).Cotangent) = r

namespace Coordinates

open MvPolynomial

private def polynomialConormalBasis (R σ : Type*) [CommRing R] :
    Module.Basis σ R (RingHom.ker (polynomialAugmentation σ R)).Cotangent := by
  letI : Algebra (MvPolynomial σ R) R := (polynomialAugmentation σ R).toAlgebra
  letI : IsScalarTower R (MvPolynomial σ R) R :=
    IsScalarTower.of_algebraMap_eq' (polynomialAugmentation σ R).comp_algebraMap.symm
  exact ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange R).map
    (AugmentationCotangent.cotangentEquivTensor R (MvPolynomial σ R)).symm

private theorem polynomialConormalBasis_apply (R σ : Type*) [CommRing R] (i : σ) :
    polynomialConormalBasis R σ i = AugmentedAlgebra.classMap (polynomialAugmentation σ R) (X i) := by
  let : Algebra (MvPolynomial σ R) R := (polynomialAugmentation σ R).toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) R :=
    IsScalarTower.of_algebraMap_eq' (polynomialAugmentation σ R).comp_algebraMap.symm
  change (((KaehlerDifferential.mvPolynomialBasis R σ).baseChange R).map
    (AugmentationCotangent.cotangentEquivTensor R (MvPolynomial σ R)).symm) i = _
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact AugmentationCotangent.fromTensor_tmul_D R (MvPolynomial σ R) 1 (X i) |>.trans (one_smul _ _)

private theorem jetMap_bijective_of_equiv {R P A : Type*} [CommRing R] [CommRing P]
    [CommRing A] [Algebra R P] [Algebra R A] {δ : P →ₐ[R] R} {ε : A →ₐ[R] R}
    (e : P ≃ₐ[R] A) (he : ε.comp e.toAlgHom = δ) (n : ℕ) :
    Function.Bijective (jetMap he n) := by
  have he' : δ.comp e.symm.toAlgHom = ε := by rw [← he]; ext p; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨jetMap he' n, ?_, ?_⟩
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ε : A →ₐ[R] R} (B : Type*) [CommRing B] [Algebra R B] (z : σ → A) (hz : ∀ i, ε (z i) = 0)

private theorem polynomial_jetMap_baseChange_bijective_iff (n : ℕ) :
    Function.Bijective (jetMap (baseChangeAugmentation_comp_map
      (aeval_preserves_augmentation z hz) B) n) ↔
    Function.Bijective (jetMap (aeval_preserves_augmentation (ε := baseChangeAugmentation ε B)
      (fun i => (1 : B) ⊗ₜ[R] z i) (fun i => by simp [hz i])) n) := by
  let e : MvPolynomial σ B ≃ₐ[B] B ⊗[R] MvPolynomial σ R :=
    (MvPolynomial.algebraTensorAlgEquiv R B).symm
  have he : (baseChangeAugmentation (polynomialAugmentation σ R) B).comp e.toAlgHom =
      polynomialAugmentation σ B := by
    ext i
    simp [e, polynomialAugmentation]
  let f : B ⊗[R] MvPolynomial σ R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) (aeval z)
  have hf : f.comp e.toAlgHom = aeval (fun i => (1 : B) ⊗ₜ[R] z i) := by
    ext i
    simp [e, f]
  have hcomp : ⇑(jetMap (baseChangeAugmentation_comp_map
      (aeval_preserves_augmentation z hz) B) n) ∘ jetMap he n =
      ⇑(jetMap (aeval_preserves_augmentation (ε := baseChangeAugmentation ε B)
        (fun i => (1 : B) ⊗ₜ[R] z i)
        (fun i => by simp [hz i])) n) := by
    funext p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    simp only [Function.comp_apply, jetMap_mk]
    exact congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun hf p)
  rw [← hcomp]
  exact (Function.Bijective.of_comp_iff _ (jetMap_bijective_of_equiv e he n)).symm

include hz in
private theorem span_conormal_baseChange
    (hspan : Submodule.span R (Set.range (AugmentedAlgebra.classMap ε ∘ z)) = ⊤) :
    Submodule.span B (Set.range (fun i =>
      AugmentedAlgebra.classMap (baseChangeAugmentation ε B) ((1 : B) ⊗ₜ[R] z i))) = ⊤ := by
  let v : σ → (RingHom.ker ε).Cotangent := AugmentedAlgebra.classMap ε ∘ z
  let w : σ → (RingHom.ker (baseChangeAugmentation ε B)).Cotangent :=
    fun i => AugmentedAlgebra.classMap (baseChangeAugmentation ε B) ((1 : B) ⊗ₜ[R] z i)
  have hs : Submodule.span R (Set.range v) = ⊤ := hspan
  have h := congrArg (Submodule.baseChange B) hs
  rw [Submodule.baseChange_span, Submodule.baseChange_top] at h
  let e := baseChangeConormalEquiv ε B
  have hm : (Submodule.span B ((TensorProduct.mk R B _ 1) '' Set.range v)).map e.toLinearMap =
      (⊤ : Submodule B _).map e.toLinearMap := congrArg (Submodule.map e.toLinearMap) h
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range,
    ← Set.range_comp, ← Set.range_comp] at hm
  have hw : (⇑e.toLinearMap ∘ ⇑(TensorProduct.mk R B _ 1) ∘ v) = w := by
    funext i
    exact baseChangeConormalEquiv_tmul_classMap ε B 1 (z i) (hz i)
  rw [hw] at hm
  exact hm

private theorem finrank_fiber_of_basis {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] {r : ℕ} (b : Module.Basis (Fin r) S M) (p : PrimeSpectrum S) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = r := by
  simpa using Module.finrank_eq_card_basis (b.baseChange p.asIdeal.ResidueField)

universe u v w

/-- For fixed conormal generators on a noetherian affine base, the coefficient
ideal of the section jet maps cuts out smoothness of that rank on every affine test. -/
def SectionJetSmoothRankLocusStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R A]
    (ε : A →ₐ[R] R) (r : ℕ) (z : Fin r → A) (hz : ∀ i, ε (z i) = 0),
    Submodule.span R (Set.range (AugmentedAlgebra.classMap ε ∘ z)) = ⊤ →
      (jetIsomorphismIdeal (aeval_preserves_augmentation z hz) ≤ RingHom.ker (algebraMap R B) ↔
        SmoothAlongSectionOfRank (baseChangeAugmentation ε B) r)

theorem sectionJetSmoothRankLocus : SectionJetSmoothRankLocusStatement.{u, v, w} := by
  intro R A B _ _ _ _ _ _ _ ε r z hz hspan
  let P := MvPolynomial (Fin r) R
  let f : P →ₐ[R] A := aeval z
  let h := aeval_preserves_augmentation z hz
  let εB := baseChangeAugmentation ε B
  let zB : Fin r → B ⊗[R] A := fun i => (1 : B) ⊗ₜ[R] z i
  have hzB (i : Fin r) : εB (zB i) = 0 := by simp [εB, zB, hz i]
  have hsurj := sectionJetPolynomialSurjectivity R A (Fin r) ε z hz hspan
  have hj := sectionJetIsomorphismLocus R P A B (polynomialAugmentation (Fin r) R) ε f h hsurj
  let hB := aeval_preserves_augmentation zB hzB
  let g := conormalMap hB
  let b := polynomialConormalBasis B (Fin r)
  have hb (i : Fin r) : g (b i) = AugmentedAlgebra.classMap εB (zB i) := by
    rw [polynomialConormalBasis_apply]
    rw [conormalMap_classMap hB (X i) (by simp [polynomialAugmentation]), aeval_X]
  constructor
  · intro hI
    obtain ⟨a, ha, haSmooth⟩ := sectionJetSmoothNeighborhood R P A B
      (polynomialAugmentation (Fin r) R) ε f h hsurj hI
    have hg : Function.Bijective g := (jetMap_one_bijective_iff hB).mp <|
      (polynomial_jetMap_baseChange_bijective_iff B z hz 1).mp (hj.mp hI 1)
    refine ⟨?_, finrank_fiber_of_basis (b.map (LinearEquiv.ofBijective g hg))⟩
    intro p hp
    let q := PrimeSpectrum.comap εB.toRingHom ⟨p, hp⟩
    have hq : q ∈ PrimeSpectrum.basicOpen a := by
      rw [PrimeSpectrum.mem_basicOpen]
      change εB a ∉ p
      rw [ha]
      exact hp.one_notMem
    exact basicOpen_subset_smoothLocus_iff_smooth.mpr haSmooth hq
  · rintro ⟨hSmooth, hRank⟩
    obtain ⟨a, ha, haSmooth⟩ := exists_smooth_away_of_section εB hSmooth
    let : Smooth B (Localization.Away a) := haSmooth
    let := projective_cotangent_of_smooth_away εB a (ha ▸ isUnit_one)
    let := finite_cotangent_of_finiteType εB
    let := finite_cotangent_of_finiteType (polynomialAugmentation (Fin r) B)
    let := Module.Free.of_basis b
    have hg : Function.Surjective g := by
      rw [← LinearMap.range_eq_top, ← Submodule.map_top, ← b.span_eq, Submodule.map_span,
        ← Set.range_comp]
      have he : (⇑g ∘ ⇑b) = fun i =>
          (show (RingHom.ker εB).Cotangent from AugmentedAlgebra.classMap εB (zB i)) := funext hb
      rw [he]
      exact span_conormal_baseChange B z hz hspan
    have hbij : Function.Bijective g :=
      Module.bijective_of_surjective_of_rankAtStalk_eq hg fun m _ => by
        rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq, finrank_fiber_of_basis b, hRank]
    refine hj.mpr fun n => (polynomial_jetMap_baseChange_bijective_iff B z hz n).mpr ?_
    exact sectionJetCoordinatesOfSmoothNeighborhood B (B ⊗[R] A) (Fin r) εB zB hzB
      (b.map (LinearEquiv.ofBijective g hbij)) (fun i => (hb i).symm) a (ha ▸ isUnit_one) n

end Coordinates
end Algebra.SectionJet
