import Langlands.Algebra.ProjectiveTensorCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine closed loci of projective tensor equations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

open Langlands.Algebra.ProjectiveTensorCoefficients

/-- A map to an affine quotient exists exactly when the defining ideal is
annihilated on global sections, for an arbitrary test scheme. -/
theorem factorsThrough_affineQuotient_iff {A : CommRingCat.{u}} {T : Scheme.{u}}
    (J : Ideal A) (t : T ⟶ Spec A) :
    (∃ z : T ⟶ Spec (CommRingCat.of (A ⧸ J)),
      z ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = t) ↔
      J ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ t.appTop).hom := by
  constructor
  · rintro ⟨z, rfl⟩ a ha
    apply RingHom.mem_ker.mpr
    rw [Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    change ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv ≫ z.appTop).hom
      (Ideal.Quotient.mk J a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro h
    exact ⟨t.liftQuotient J h, t.liftQuotient_comp J h⟩

variable {R P A B : Type u} [CommRing R]
  [AddCommGroup P] [Module R P]
  [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

/-- The affine scheme cut out by all coefficients of the selected tensors. -/
def tensorCoefficientLocus (I : Set (A ⊗[R] P)) : Scheme.{u} :=
  Spec (CommRingCat.of (A ⧸ coefficientIdeal I))

/-- The inclusion of the coefficient locus into the affine coefficient scheme. -/
def tensorCoefficientLocusι (I : Set (A ⊗[R] P)) :
    tensorCoefficientLocus I ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coefficientIdeal I)))

instance tensorCoefficientLocusι_isClosedImmersion (I : Set (A ⊗[R] P)) :
    IsClosedImmersion (tensorCoefficientLocusι I) :=
  IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) (coefficientIdeal I)

/-- On every test scheme, factorization through the actual coefficient locus
is equivalent to annihilation of every dual contraction. -/
theorem factorsThrough_tensorCoefficientLocus_iff
    (I : Set (A ⊗[R] P)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A)) :
    (∃ z : T ⟶ tensorCoefficientLocus I, z ≫ tensorCoefficientLocusι I = t) ↔
      ∀ x ∈ I, ∀ φ : P →ₗ[R] R,
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ t.appTop).hom (contract φ x) = 0 := by
  change (∃ z : T ⟶ Spec (CommRingCat.of (A ⧸ coefficientIdeal I)),
    z ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coefficientIdeal I))) = t) ↔ _
  rw [factorsThrough_affineQuotient_iff (A := CommRingCat.of A),
    coefficientIdeal, Ideal.span_le]
  constructor
  · intro h x hx φ
    exact (RingHom.mem_ker
      (f := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ t.appTop).hom)).mp
        (h ⟨x, hx, φ, rfl⟩)
  · rintro h a ⟨x, hx, φ, rfl⟩
    exact RingHom.mem_ker.mpr (h x hx φ)

/-- For affine test schemes, the coefficient locus represents simultaneous
vanishing after an arbitrary coefficient-algebra map. -/
theorem affine_factorsThrough_tensorCoefficientLocus_iff [Module.Projective R P]
    (I : Set (A ⊗[R] P)) (f : A →ₐ[R] B) :
    (∃ z : Spec (CommRingCat.of B) ⟶ tensorCoefficientLocus I,
      z ≫ tensorCoefficientLocusι I = Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
      ∀ x ∈ I, f.toLinearMap.rTensor P x = 0 := by
  change (∃ z : Spec (CommRingCat.of B) ⟶
    Spec (CommRingCat.of (A ⧸ coefficientIdeal I)),
    z ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coefficientIdeal I))) =
      Spec.map (CommRingCat.ofHom f.toRingHom)) ↔ _
  rw [factorsThrough_affineQuotient_iff (A := CommRingCat.of A),
    ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp]
  change coefficientIdeal I ≤ RingHom.ker
    ((Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.toRingHom.comp
      f.toRingHom) ↔ _
  erw [RingHom.ker_comp_of_injective f.toRingHom
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.injective]
  exact coefficientIdeal_le_ker_iff I f

end Langlands.AlgebraicGeometry
