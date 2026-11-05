import Langlands.AlgebraicGeometry.Deformation.CompletedLocalPolynomialSource
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Jacobson.Ring

/-! # Surjective complete local polynomial presentations of actual Artinian tests -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianPolynomialPresentation

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  (A : ArtinianTest k K)

/-- A finite residue algebra makes the entire actual Artinian test finite over
the original scalar ring, without a coefficient-field section. -/
lemma moduleFinite [Module.Finite k K] : Module.Finite k A.algebra := by
  apply Module.finite_of_surjective_of_ker_le_nilradical A.augmentation
    A.augmentation_surjective
  · exact (RingHom.ker A.augmentation.toRingHom).fg_of_isNoetherianRing
      |>.isNilpotent_iff_le_nilradical.mp A.augmentation_ker_isNilpotent
  · exact (RingHom.ker A.augmentation.toRingHom).fg_of_isNoetherianRing

variable [Module.Finite k K]

/-- A finite polynomial presentation of the actual whole test algebra.
The index stays in the universe of the original test. -/
def polynomialPresentation :
    Σ d : ℕ, {φ : MvPolynomial (ULift.{u} (Fin d)) k →ₐ[k] A.algebra //
      Function.Surjective φ} := by
  have := moduleFinite A
  have h := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A.algebra)
  let d := Classical.choose h
  let φ := Classical.choose (Classical.choose_spec h)
  have hφ : Function.Surjective φ := Classical.choose_spec (Classical.choose_spec h)
  let e := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  exact ⟨d, φ.comp e.toAlgHom, hφ.comp e.surjective⟩

/-- The finite variable index of the chosen presentation of the whole test. -/
abbrev Index := ULift.{u} (Fin (polynomialPresentation A).1)

/-- The actual chosen surjective polynomial map onto the whole test algebra. -/
abbrev polynomialCover : MvPolynomial (Index A) k →ₐ[k] A.algebra :=
  (polynomialPresentation A).2.val

lemma polynomialCover_surjective : Function.Surjective (polynomialCover A) :=
  (polynomialPresentation A).2.property

/-- The residue map of the same polynomial presentation. -/
abbrev polynomialAugmentation : MvPolynomial (Index A) k →ₐ[k] K :=
  A.augmentation.comp (polynomialCover A)

lemma polynomialAugmentation_surjective :
    Function.Surjective (polynomialAugmentation A) :=
  A.augmentation_surjective.comp (polynomialCover_surjective A)

/-- The actual local polynomial source of this presentation. -/
abbrev localRing := LocalPolynomialArtinianSource.ring (polynomialAugmentation A)

/-- The chosen polynomial generators extend to the local source, using the
given augmentation to detect all required units. -/
def localCover :
    LocalPolynomialArtinianSource.Maps (polynomialAugmentation A) A :=
  LocalPolynomialArtinianSource.extend (polynomialAugmentation A) A
    ⟨fun i ↦ polynomialCover A (MvPolynomial.X i), fun _ ↦ rfl⟩

lemma localCover_polynomialMap :
    (localCover A).val.comp
      (LocalPolynomialArtinianSource.polynomialMap (polynomialAugmentation A)) =
        polynomialCover A := by
  rw [localCover, LocalPolynomialArtinianSource.extend_polynomialMap]
  apply MvPolynomial.algHom_ext
  intro i
  exact MvPolynomial.aeval_X _ i

lemma localCover_surjective : Function.Surjective (localCover A).val := by
  intro a
  obtain ⟨p, hp⟩ := polynomialCover_surjective A a
  refine ⟨LocalPolynomialArtinianSource.polynomialMap (polynomialAugmentation A) p, ?_⟩
  exact (DFunLike.congr_fun (localCover_polynomialMap A) p).trans hp

variable [IsNoetherianRing k]

/-- The actual complete noetherian local polynomial source surjecting onto the
whole Artinian test. -/
abbrev ring := CompletedLocalPolynomialSource.ring (polynomialAugmentation A)

/-- The specified residue augmentation of the actual complete source. -/
abbrev augmentation : ring A →ₐ[k] K :=
  CompletedLocalPolynomialSource.augmentation (polynomialAugmentation A)
    (polynomialAugmentation_surjective A)

omit [IsNoetherianRing k] in
lemma augmentation_surjective : Function.Surjective (augmentation A) :=
  CompletedLocalPolynomialSource.augmentation_surjective _ _

/-- The chosen local presentation extends to the actual maximal-ideal
completion, with its original residue equation. -/
def completedCover :
    CompletedLocalPolynomialSource.Maps (polynomialAugmentation A)
      (polynomialAugmentation_surjective A) A :=
  (CompletedLocalPolynomialSource.localMapEquiv (polynomialAugmentation A)
    (polynomialAugmentation_surjective A) A).symm (localCover A)

/-- The scalar-preserving map from the actual complete source onto the test. -/
abbrev cover : ring A →ₐ[k] A.algebra := (completedCover A).val

lemma augmentation_cover : A.augmentation.comp (cover A) = augmentation A :=
  (completedCover A).property

/-- The completed cover recovers exactly the original local presentation. -/
lemma cover_sourceMap :
    (cover A).comp (CompletedLocalPolynomialSource.sourceMap
      (polynomialAugmentation A)) = (localCover A).val := by
  have h := (CompletedLocalPolynomialSource.localMapEquiv (polynomialAugmentation A)
    (polynomialAugmentation_surjective A) A).apply_symm_apply (localCover A)
  exact congrArg Subtype.val h

/-- The original polynomial generators still have their prescribed actual
values under the completed cover. -/
lemma cover_polynomialMap :
    (cover A).comp (CompletedLocalPolynomialSource.polynomialMap
      (polynomialAugmentation A)) = polynomialCover A := by
  rw [CompletedLocalPolynomialSource.polynomialMap, ← AlgHom.comp_assoc,
    cover_sourceMap, localCover_polynomialMap]

/-- Completion retains surjectivity onto the actual whole Artinian test. -/
lemma cover_surjective : Function.Surjective (cover A) := by
  intro a
  obtain ⟨p, hp⟩ := polynomialCover_surjective A a
  refine ⟨CompletedLocalPolynomialSource.polynomialMap (polynomialAugmentation A) p, ?_⟩
  exact (DFunLike.congr_fun (cover_polynomialMap A) p).trans hp

/-- The actual equation ideal cutting out the given Artinian test. -/
abbrev equations : Ideal (ring A) := RingHom.ker (cover A).toRingHom

/-- This equation ideal is finitely generated in the actual complete source. -/
lemma equations_fg : (equations A).FG :=
  (equations A).fg_of_isNoetherianRing

/-- The equations vanish at the specified residue augmentation. -/
lemma equations_le_maximalIdeal :
    equations A ≤ IsLocalRing.maximalIdeal (ring A) := by
  rw [← IsLocalRing.ker_eq_maximalIdeal (augmentation A).toRingHom
    (augmentation_surjective A)]
  intro r hr
  change augmentation A r = 0
  rw [← augmentation_cover]
  change A.augmentation (cover A r) = 0
  have hr' : cover A r = 0 := RingHom.mem_ker.mp hr
  rw [hr', map_zero]

/-- Some positive maximal-ideal power belongs to the actual equation ideal. -/
lemma exists_power_le_equations :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (ring A) ^ (n + 1) ≤ equations A :=
  LocalAdicArtinianTests.exists_bound (augmentation A) (augmentation_surjective A)
    (cover A) (augmentation_cover A)

/-- The original actual test is the quotient by the actual equations, with the
original scalar action retained. -/
def quotientEquiv : (ring A ⧸ equations A) ≃ₐ[k] A.algebra :=
  Ideal.quotientKerAlgEquivOfSurjective (cover_surjective A)

@[simp]
lemma quotientEquiv_mk (r : ring A) :
    quotientEquiv A (Ideal.Quotient.mk (equations A) r) = cover A r := rfl

/-- The quotient presentation recovers the specified residue map exactly. -/
lemma quotientEquiv_augmentation (r : ring A) :
    A.augmentation (quotientEquiv A (Ideal.Quotient.mk (equations A) r)) =
      augmentation A r :=
  DFunLike.congr_fun (augmentation_cover A) r

section FiniteTypeResidue

variable (k K) [IsJacobsonRing k] [Algebra.FiniteType k K]

omit [Module.Finite k K] [IsNoetherianRing k] in
/-- In particular, a finite type field residue over a Jacobson scalar ring
makes every actual Artinian test finite over that scalar ring. -/
lemma moduleFinite_of_finiteType (A : ArtinianTest k K) : Module.Finite k A.algebra := by
  have := finite_of_finite_type_of_isJacobsonRing k K
  exact moduleFinite A

end FiniteTypeResidue

end Langlands.AlgebraicGeometry.Deformation.ArtinianPolynomialPresentation
