import Langlands.RingTheory.Smooth.SectionJetLocalization
import Langlands.RingTheory.Smooth.SectionJetPolynomialSurjectivity

/-! # Conormal maps and polynomial coordinates near a section -/

noncomputable section

universe u v w t

namespace Algebra.SectionJet

open Langlands.GroupScheme.CoordinateWeights

section ConormalMap

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [CommRing A] [Algebra R P] [Algebra R A]
  {δ : P →ₐ[R] R} {ε : A →ₐ[R] R} {f : P →ₐ[R] A} (hf : ε.comp f = δ)

/-- The map of augmentation conormal modules induced by an augmented map. -/
def conormalMap : (RingHom.ker δ).Cotangent →ₗ[R] (RingHom.ker ε).Cotangent :=
  Ideal.mapCotangent _ _ f (by simpa only [pow_one] using ker_pow_le_comap hf 1)

theorem conormalMap_classMap (x : P) (hx : δ x = 0) :
    conormalMap hf (AugmentedAlgebra.classMap δ x) =
      AugmentedAlgebra.classMap ε (f x) := by
  have hx' : ε (f x) = 0 := (AlgHom.congr_fun hf x).trans hx
  rw [AugmentedAlgebra.classMap_ideal δ ⟨x, hx⟩,
    AugmentedAlgebra.classMap_ideal ε ⟨f x, hx'⟩]
  rfl

theorem conormalMap_surjective (h : Function.Surjective f) :
    Function.Surjective (conormalMap hf) := by
  intro y
  obtain ⟨⟨a, ha⟩, rfl⟩ := (RingHom.ker ε).toCotangent_surjective y
  obtain ⟨x, rfl⟩ := h a
  have hx : δ x = 0 := (AlgHom.congr_fun hf x).symm.trans ha
  exact ⟨(RingHom.ker δ).toCotangent ⟨x, hx⟩, rfl⟩

private theorem jetMap_cotangentEquivLayer (x : (RingHom.ker δ).Cotangent) :
    jetMap hf 1 (cotangentEquivLayer δ x).val =
      (cotangentEquivLayer ε (conormalMap hf x)).val := by
  obtain ⟨y, rfl⟩ := (RingHom.ker δ).toCotangent_surjective x
  rfl

/-- The map on first jets is bijective exactly when the conormal map is bijective. -/
theorem jetMap_one_bijective_iff :
    Function.Bijective (jetMap hf 1) ↔ Function.Bijective (conormalMap hf) := by
  have h :
      ⇑(jetMap hf 1) ∘ ⇑(firstSplitEquiv δ).symm =
        ⇑(firstSplitEquiv ε).symm ∘ Prod.map _root_.id (conormalMap hf) := by
    funext x
    change jetMap hf 1 (algebraMap R _ x.1 + (cotangentEquivLayer δ x.2).val) =
      algebraMap R _ x.1 + (cotangentEquivLayer ε (conormalMap hf x.2)).val
    rw [map_add, AlgHom.commutes, jetMap_cotangentEquivLayer]
  rw [← Function.Bijective.of_comp_iff (jetMap hf 1) (firstSplitEquiv δ).symm.bijective, h,
    (firstSplitEquiv ε).symm.bijective.of_comp_iff', Prod.map_bijective]
  exact and_iff_right (Function.bijective_id)

end ConormalMap

/-- The conormal module of a finite type augmented algebra is finite over the base. -/
theorem finite_cotangent_of_finiteType {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] [FiniteType R A] (ε : A →ₐ[R] R) :
    Module.Finite R (RingHom.ker ε).Cotangent := by
  obtain ⟨n, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp
    inferInstance
  exact Module.Finite.of_surjective (conormalMap (f := f) (ε := ε) rfl)
    (conormalMap_surjective rfl hf)

/-- The conormal module is projective if the section has a smooth principal neighborhood. -/
theorem projective_cotangent_of_smooth_away {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
    (a : A) (ha : IsUnit (ε a)) [Smooth R (Localization.Away a)] :
    Module.Projective R (RingHom.ker ε).Cotangent := by
  let h := awayAugmentation_comp ε a ha
  let e := LinearEquiv.ofBijective (conormalMap h)
    ((jetMap_one_bijective_iff h).mp (sectionJetLocalization R A ε a ha 1))
  let := projective_cotangent (awayAugmentation ε a ha)
  exact Module.Projective.of_equiv e.symm

namespace Coordinates

open MvPolynomial

variable {R : Type u} {A : Type w} {σ : Type t} [CommRing R] [CommRing A] [Algebra R A]
  {ε : A →ₐ[R] R} (z : σ → A) (hz : ∀ i, ε (z i) = 0)

/-- If conormal coordinate lifts give a basis and the section admits a
smooth principal neighborhood, the coordinate map is bijective on every jet. -/
def SectionJetCoordinatesOfSmoothNeighborhoodStatement : Prop :=
  ∀ (R : Type u) (A : Type w) (σ : Type t) [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (z : σ → A) (hz : ∀ i, ε (z i) = 0)
    (b : Module.Basis σ R (RingHom.ker ε).Cotangent),
    (∀ i, AugmentedAlgebra.classMap ε (z i) = b i) →
    ∀ (a : A), IsUnit (ε a) → [Smooth R (Localization.Away a)] →
      ∀ n : ℕ, Function.Bijective (jetMap (aeval_preserves_augmentation z hz) n)

theorem sectionJetCoordinatesOfSmoothNeighborhood :
    SectionJetCoordinatesOfSmoothNeighborhoodStatement.{u, w, t} := by
  intro R A σ _ _ _ ε z hz b hb a ha _ n
  let L := Localization.Away a
  let εL := awayAugmentation ε a ha
  let hL := awayAugmentation_comp ε a ha
  let f := Algebra.algHom R A L
  let e := LinearEquiv.ofBijective (conormalMap hL)
    ((jetMap_one_bijective_iff hL).mp (sectionJetLocalization R A ε a ha 1))
  let zL := f ∘ z
  have hzL (i : σ) : εL (zL i) = 0 := (AlgHom.congr_fun hL (z i)).trans (hz i)
  have hbL (i : σ) : AugmentedAlgebra.classMap εL (zL i) = b.map e i := by
    rw [Module.Basis.map_apply]
    have h₁ : AugmentedAlgebra.classMap εL (zL i) =
        conormalMap hL (AugmentedAlgebra.classMap ε (z i)) :=
      (conormalMap_classMap hL (z i) (hz i)).symm
    have h₂ : conormalMap hL (AugmentedAlgebra.classMap ε (z i)) = e (b i) :=
      congrArg (conormalMap hL) (hb i)
    exact h₁.trans h₂
  let ℓ := jetMap hL n
  have hℓ : Function.Bijective ℓ := sectionJetLocalization R A ε a ha n
  apply (hℓ.of_comp_iff' (jetMap (aeval_preserves_augmentation z hz) n)).mp
  let eq := jetEquiv zL (b.map e) hzL hbL n
  let q := Ideal.quotientEquivAlgOfEq R
    (congrArg (· ^ (n + 1)) (ker_polynomialAugmentation σ R))
  have h :
      ⇑ℓ ∘ ⇑(jetMap (aeval_preserves_augmentation z hz) n) = ⇑eq ∘ ⇑q := by
    funext p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    change Ideal.Quotient.mk _ (f (aeval z p)) = Ideal.Quotient.mk _ (aeval zL p)
    have hφ : f.comp (aeval z) = aeval zL := by ext i; simp [zL]
    rw [← hφ, AlgHom.comp_apply]
  rw [h]
  exact eq.bijective.comp q.bijective

end Coordinates
end Algebra.SectionJet
