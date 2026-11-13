import Langlands.AlgebraicGeometry.Picard.AffineBaseMaps
import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Affine-base arrows and Artinian tests from truncations of a finite-type algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation

namespace AffineQuotientTests

section AffineMaps

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

export OpennessOfVersality (exists_affineBaseMap_eq)

/-- The affine-base arrow determines its algebra map. -/
lemma affineBaseMap_injective {a b : A →ₐ[k] B} (h : affineBaseMap a = affineBaseMap b) :
    a = b := by
  have h1 := congrArg (fun g => g.left) h
  simp only [affineBaseMap] at h1
  have h2 := Spec.map_injective h1
  ext x
  exact congrArg (fun f => f.hom x) h2

/-- Surjective algebra maps give monomorphic affine-base arrows. -/
lemma mono_affineBaseMap {a : A →ₐ[k] B} (ha : Function.Surjective a) :
    Mono (affineBaseMap a) := by
  have : Mono (affineBaseMap a).left := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ ha
    change Mono (Spec.map (CommRingCat.ofHom a.toRingHom))
    infer_instance
  refine ⟨fun g h hgh => ?_⟩
  apply Over.OverMorphism.ext
  rw [← cancel_mono (affineBaseMap a).left]
  exact congrArg (fun f => f.left) hgh

end AffineMaps

/-- A ring with a surjection onto a field whose kernel consists of nilpotents is local. -/
lemma isLocalRing_of_surjective_of_isNilpotent {Q K : Type*} [CommRing Q] [Field K]
    (f : Q →+* K) (hf : Function.Surjective f)
    (hnil : ∀ x, f x = 0 → IsNilpotent x) : IsLocalRing Q := by
  have : Nontrivial Q := f.domain_nontrivial
  have hunit : ∀ x, f x ≠ 0 → IsUnit x := by
    intro x hx
    obtain ⟨y, hy⟩ := hf (f x)⁻¹
    have h1 : f (x * y - 1) = 0 := by rw [map_sub, map_mul, hy, mul_inv_cancel₀ hx, map_one, sub_self]
    have h2 : IsUnit (x * y) := by
      have := (hnil _ h1).isUnit_one_add
      simpa using this
    exact isUnit_of_mul_isUnit_left h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : f a = 0
  · right
    apply hunit
    rw [map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · left
    exact hunit a ha

section Tests

variable {k K T : Type u} [CommRing k] [Field K] [Algebra k K] [CommRing T] [Algebra k T]
  [IsNoetherianRing T] (εT : T →ₐ[k] K) (hεT : Function.Surjective εT)

/-- The augmentation of the truncation `T / m ^ (n + 1)`, `m = ker εT`. -/
def augmentation (n : ℕ) : T ⧸ RingHom.ker εT ^ (n + 1) →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ εT (fun _ hx =>
    RingHom.mem_ker.mp (Ideal.pow_le_self (Nat.succ_ne_zero n) hx))

omit [IsNoetherianRing T] in
lemma augmentation_mk (n : ℕ) (x : T) :
    augmentation εT n (Ideal.Quotient.mk _ x) = εT x := rfl

include hεT

omit [IsNoetherianRing T] in
lemma augmentation_surjective (n : ℕ) : Function.Surjective (augmentation εT n) := by
  intro y
  obtain ⟨x, rfl⟩ := hεT y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

omit [IsNoetherianRing T] in
lemma isLocalRing_quotient (n : ℕ) : IsLocalRing (T ⧸ RingHom.ker εT ^ (n + 1)) := by
  refine isLocalRing_of_surjective_of_isNilpotent (augmentation εT n).toRingHom
    (augmentation_surjective εT hεT n) fun x hx => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hy : εT y = 0 := hx
  exact Ideal.pow_mem_pow (RingHom.mem_ker.mpr hy) _

lemma isArtinianRing_quotient (n : ℕ) : IsArtinianRing (T ⧸ RingHom.ker εT ^ (n + 1)) := by
  have := isLocalRing_quotient εT hεT n
  have hker : RingHom.ker (augmentation εT n).toRingHom =
      IsLocalRing.maximalIdeal (T ⧸ RingHom.ker εT ^ (n + 1)) :=
    IsLocalRing.ker_eq_maximalIdeal _ (augmentation_surjective εT hεT n)
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨n + 1, ?_⟩
  rw [← hker]
  have : RingHom.ker (augmentation εT n).toRingHom =
      (RingHom.ker εT).map (Ideal.Quotient.mk (RingHom.ker εT ^ (n + 1))) := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker]
    change εT y = 0 ↔ _
    rw [← RingHom.mem_ker, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (Ideal.pow_le_self (Nat.succ_ne_zero n))]
  rw [this, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

/-- The augmented Artinian test `T / m ^ (n + 1)`. -/
def test (n : ℕ) : ArtinianTest k K := by
  have := isLocalRing_quotient εT hεT n
  have := isArtinianRing_quotient εT hεT n
  exact ArtinianTest.mk (T ⧸ RingHom.ker εT ^ (n + 1)) (augmentation εT n)
    (augmentation_surjective εT hεT n)

/-- The transition between consecutive truncations. -/
def transition (n : ℕ) : test εT hεT (n + 1) ⟶ test εT hεT n :=
  ArtinianTest.homMk
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (by apply Ideal.Quotient.algHom_ext; ext x; rfl)

lemma transition_surjective (n : ℕ) :
    Function.Surjective (ArtinianTest.toAlgHom (transition εT hεT n)) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The truncation map of `T` as an arrow of affine bases. -/
def level (n : ℕ) : ArtinianTest.base (test εT hεT n) ⟶ affineBase k T :=
  affineBaseMap (Ideal.Quotient.mkₐ k (RingHom.ker εT ^ (n + 1)))

lemma baseMap_transition_level (n : ℕ) :
    ArtinianTest.baseMap (transition εT hεT n) ≫ level εT hεT (n + 1) = level εT hεT n := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (ArtinianTest.toAlgHom (transition εT hεT n)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (RingHom.ker εT ^ (n + 1 + 1))).toRingHom) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (RingHom.ker εT ^ (n + 1))).toRingHom)
  rw [← Spec.map_comp]
  rfl

end Tests

section ResiduePoint

variable {k K T : Type u} [CommRing k] [Field K] [Algebra k K] [CommRing T] [Algebra k T]

/-- A surjection onto a field gives a point of `Spec T` whose residue field is identified
with the field, compatibly with the given map. -/
lemma exists_residueField_iso (εT : T →ₐ[k] K) (hεT : Function.Surjective εT) :
    ∃ (u₀ : (affineBase k T).left) (e : (affineBase k T).left.residueField u₀ ≅ CommRingCat.of K),
      Spec.map (CommRingCat.ofHom εT.toRingHom) =
        Spec.map e.hom ≫ (affineBase k T).left.fromSpecResidueField u₀ := by
  let xf := Scheme.SpecToEquivOfField K (Spec (CommRingCat.of T))
    (Spec.map (CommRingCat.ofHom εT.toRingHom))
  have hg : Spec.map xf.2 ≫ (Spec (CommRingCat.of T)).fromSpecResidueField xf.1 =
      Spec.map (CommRingCat.ofHom εT.toRingHom) :=
    (Scheme.SpecToEquivOfField K _).symm_apply_apply _
  have : xf.1.asIdeal.IsPrime := PrimeSpectrum.isPrime xf.1
  have hring : CommRingCat.ofHom εT.toRingHom =
      CommRingCat.ofHom (algebraMap T xf.1.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of T) xf.1).inv ≫ xf.2 := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    exact hg.symm
  have hsurj : Function.Surjective xf.2 := by
    intro y
    obtain ⟨t, rfl⟩ := hεT y
    refine ⟨(Scheme.Spec.residueFieldIso (CommRingCat.of T) xf.1).inv
      (algebraMap T xf.1.asIdeal.ResidueField t), ?_⟩
    have := congrArg (fun φ => φ.hom t) hring
    simpa using this.symm
  let e : (Spec (CommRingCat.of T)).residueField xf.1 ≅ CommRingCat.of K :=
    (RingEquiv.ofBijective xf.2.hom ⟨xf.2.hom.injective, hsurj⟩).toCommRingCatIso
  exact ⟨xf.1, e, hg.symm⟩

end ResiduePoint

end AffineQuotientTests

end Langlands.AlgebraicGeometry.Picard
