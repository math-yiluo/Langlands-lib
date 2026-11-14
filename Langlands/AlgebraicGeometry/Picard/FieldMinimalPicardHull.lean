import Langlands.AlgebraicGeometry.Picard.FiniteBasisPicardTangentLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceCompletion
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerAlgebraization
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerRingLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerTangentLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPrincipalLifting
import Langlands.AlgebraicGeometry.Deformation.CompletedLocalPolynomialSource

/-! # A minimal formally versal Picard hull over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FieldMinimalPicardHull

open Langlands.AlgebraicGeometry.Deformation
open ArtinianPicardSourceTower ArtinianPicardTowerAlgebraization

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f] (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k k)))

/-- The basis directions of the split tangent test. -/
abbrev Index := FiniteBasisPicardFamily.Index f M

/-- The actual split tangent test of the finite basis family. -/
abbrev test : ArtinianTest k k := FiniteBasisPicardFamily.test f M

/-- The `i`-th square-zero direction of the tangent test. -/
def direction (i : Index f M) : (test f M).algebra :=
  (TrivSqZeroExt.inr (Pi.single i (1 : k)) : TrivSqZeroExt k (Index f M → k))

/-- The polynomial presentation sending the `i`-th variable to the `i`-th direction. -/
def polynomialCover : MvPolynomial (Index f M) k →ₐ[k] (test f M).algebra :=
  MvPolynomial.aeval (direction f M)

lemma polynomialCover_surjective : Function.Surjective (polynomialCover f M) := by
  intro x
  let y : TrivSqZeroExt k (Index f M → k) := x
  let φ : MvPolynomial (Index f M) k →ₐ[k] TrivSqZeroExt k (Index f M → k) :=
    MvPolynomial.aeval (fun i ↦ TrivSqZeroExt.inr (Pi.single i (1 : k)))
  refine ⟨MvPolynomial.C y.fst + ∑ i, MvPolynomial.C (y.snd i) * MvPolynomial.X i, ?_⟩
  change φ _ = y
  simp only [φ, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_smul]
  · funext j
    simp [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul, Finset.sum_apply, Pi.single_apply]

/-- The residue map of the minimal polynomial presentation. -/
abbrev polynomialAugmentation : MvPolynomial (Index f M) k →ₐ[k] k :=
  (test f M).augmentation.comp (polynomialCover f M)

lemma polynomialAugmentation_surjective :
    Function.Surjective (polynomialAugmentation f M) :=
  (test f M).augmentation_surjective.comp (polynomialCover_surjective f M)

/-- Every variable has residue zero. -/
lemma polynomialAugmentation_X (i : Index f M) :
    polynomialAugmentation f M (MvPolynomial.X i) = 0 := by
  change ((polynomialCover f M (MvPolynomial.X i) : TrivSqZeroExt k (Index f M → k))).fst = 0
  simp [polynomialCover, direction]

/-- The minimal polynomial generators extend to the local source. -/
def localCover :
    LocalPolynomialArtinianSource.Maps (polynomialAugmentation f M) (test f M) :=
  LocalPolynomialArtinianSource.extend (polynomialAugmentation f M) (test f M)
    ⟨fun i ↦ polynomialCover f M (MvPolynomial.X i), fun _ ↦ rfl⟩

lemma localCover_polynomialMap :
    (localCover f M).val.comp
      (LocalPolynomialArtinianSource.polynomialMap (polynomialAugmentation f M)) =
        polynomialCover f M := by
  rw [localCover, LocalPolynomialArtinianSource.extend_polynomialMap]
  apply MvPolynomial.algHom_ext
  intro i
  exact MvPolynomial.aeval_X _ i

/-- The minimal complete noetherian local polynomial source. -/
abbrev ring := CompletedLocalPolynomialSource.ring (polynomialAugmentation f M)

/-- The residue augmentation of the minimal complete source. -/
abbrev augmentation : ring f M →ₐ[k] k :=
  CompletedLocalPolynomialSource.augmentation (polynomialAugmentation f M)
    (polynomialAugmentation_surjective f M)

lemma augmentation_surjective : Function.Surjective (augmentation f M) :=
  CompletedLocalPolynomialSource.augmentation_surjective _ _

/-- The minimal local presentation extended to the completion. -/
def completedCover :
    CompletedLocalPolynomialSource.Maps (polynomialAugmentation f M)
      (polynomialAugmentation_surjective f M) (test f M) :=
  (CompletedLocalPolynomialSource.localMapEquiv (polynomialAugmentation f M)
    (polynomialAugmentation_surjective f M) (test f M)).symm (localCover f M)

/-- The map from the minimal complete source onto the tangent test. -/
abbrev cover : ring f M →ₐ[k] (test f M).algebra := (completedCover f M).val

lemma augmentation_cover : (test f M).augmentation.comp (cover f M) = augmentation f M :=
  (completedCover f M).property

lemma cover_sourceMap :
    (cover f M).comp (CompletedLocalPolynomialSource.sourceMap
      (polynomialAugmentation f M)) = (localCover f M).val := by
  have h := (CompletedLocalPolynomialSource.localMapEquiv (polynomialAugmentation f M)
    (polynomialAugmentation_surjective f M) (test f M)).apply_symm_apply (localCover f M)
  exact congrArg Subtype.val h

lemma cover_polynomialMap :
    (cover f M).comp (CompletedLocalPolynomialSource.polynomialMap
      (polynomialAugmentation f M)) = polynomialCover f M := by
  rw [CompletedLocalPolynomialSource.polynomialMap, ← AlgHom.comp_assoc,
    cover_sourceMap, localCover_polynomialMap]

lemma cover_surjective : Function.Surjective (cover f M) := by
  intro a
  obtain ⟨p, hp⟩ := polynomialCover_surjective f M a
  refine ⟨CompletedLocalPolynomialSource.polynomialMap (polynomialAugmentation f M) p, ?_⟩
  exact (DFunLike.congr_fun (cover_polynomialMap f M) p).trans hp

/-- The initial pointed stage on the minimal source. -/
def stage : ArtinianPicardSourceStep.Stage (augmentation f M) f M where
  test := test f M
  cover := cover f M
  cover_surjective := cover_surjective f M
  augmentation_cover := augmentation_cover f M
  family := FiniteBasisPicardFamily.family f M

/-- Compatible maps from the minimal source lift through surjective test arrows. -/
theorem postcomp_surjective {A B : ArtinianTest k k} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    Function.Surjective (AugmentedAdicCompletion.postcomp (augmentation f M) q) :=
  CompletedLocalPolynomialSource.postcomp_surjective (polynomialAugmentation f M)
    (polynomialAugmentation_surjective f M) q hq

variable [Flat f]

/-- The hull ring: the limiting quotient of the minimal source by the tower equations. -/
abbrev hullRing := limitRing (augmentation f M) (augmentation_surjective f M) f M (stage f M)

/-- The residue augmentation of the hull ring. -/
abbrev hullAugmentation : hullRing f M →ₐ[k] k :=
  limitAugmentation (augmentation f M) (augmentation_surjective f M) f M (stage f M)

/-- The effective hull line bundle over the spectrum of the hull ring. -/
abbrev hullBundle :=
  effectiveBundle (augmentation f M) (augmentation_surjective f M) f M (stage f M)

/-- The closed point of the hull base. -/
abbrev hullPoint :=
  residuePoint (augmentation f M) (augmentation_surjective f M) f M (stage f M)

/-- The hull line bundle is formally versal at its closed point. -/
theorem isFormallyVersalAt :
    ArtinianChartVersality.IsFormallyVersalAt f (hullBundle f M) (hullPoint f M) := by
  have hTL₀ : ArtinianChartVersality.HasLiftingForAt f (stage f M).family.right.of
      (ArtinianTest.reduction (stage f M).test) (ArtinianTest.dualReduction k k) :=
    FiniteBasisPicardTangentLifting.hasLiftingForAt f M
  intro A B q hq
  exact ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting f
    (hullBundle f M) (hullPoint f M)
    (fun q hq c hc N y hy ↦
      ArtinianPicardTowerRingLifting.exists_ringLift (augmentation f M)
        (augmentation_surjective f M) f M (stage f M)
        (fun q hq ↦ postcomp_surjective f M q hq) q hq c hc N y hy)
    (ArtinianPicardTowerTangentLifting.hasLiftingForAt_dualReduction (augmentation f M)
      (augmentation_surjective f M) f M (stage f M) hTL₀) q hq

/-- The hull residue fibre is the original line bundle. -/
def hullResidueIso :
    ArtinianChartVersality.residueBundle f (hullBundle f M) (hullPoint f M) ≅ M :=
  effectiveResidueIso (augmentation f M) (augmentation_surjective f M) f M (stage f M)

/-- The `i`-th generator of the hull ring: the image of the `i`-th variable. -/
def generator (i : Index f M) : hullRing f M :=
  Ideal.Quotient.mk _
    (CompletedLocalPolynomialSource.polynomialMap (polynomialAugmentation f M) (MvPolynomial.X i))

lemma hullAugmentation_generator (i : Index f M) :
    hullAugmentation f M (generator f M i) = 0 := by
  change augmentation f M
    (CompletedLocalPolynomialSource.polynomialMap (polynomialAugmentation f M)
      (MvPolynomial.X i)) = 0
  rw [← AlgHom.comp_apply, CompletedLocalPolynomialSource.augmentation_polynomialMap]
  exact polynomialAugmentation_X f M i

/-- An augmentation-preserving map from the hull ring to a test that kills every generator
is the constant map through the residue field. -/
theorem eq_constant_of_generator {B : ArtinianTest k k}
    (ψ : hullRing f M →ₐ[k] B.algebra)
    (hψ : B.augmentation.comp ψ = hullAugmentation f M)
    (h : ∀ i, ψ (generator f M i) = 0) :
    ψ = (Algebra.ofId k B.algebra).comp (hullAugmentation f M) := by
  apply Ideal.Quotient.algHom_ext
  let α : CompletedLocalPolynomialSource.Maps (polynomialAugmentation f M)
      (polynomialAugmentation_surjective f M) B :=
    ⟨ψ.comp (Ideal.Quotient.mkₐ k _), by
      rw [← AlgHom.comp_assoc, hψ]
      rfl⟩
  let β : CompletedLocalPolynomialSource.Maps (polynomialAugmentation f M)
      (polynomialAugmentation_surjective f M) B :=
    ⟨((Algebra.ofId k B.algebra).comp (hullAugmentation f M)).comp
      (Ideal.Quotient.mkₐ k _), by
      apply AlgHom.ext
      intro a
      change B.augmentation (algebraMap k B.algebra _) = _
      rw [AlgHom.commutes]
      rfl⟩
  have hαβ : α = β := by
    apply (CompletedLocalPolynomialSource.coordinateEquiv (polynomialAugmentation f M)
      (polynomialAugmentation_surjective f M) B).injective
    apply Subtype.ext
    funext i
    rw [CompletedLocalPolynomialSource.coordinateEquiv_apply,
      CompletedLocalPolynomialSource.coordinateEquiv_apply]
    change ψ (generator f M i) =
      algebraMap k B.algebra (hullAugmentation f M (generator f M i))
    rw [h, hullAugmentation_generator, map_zero]
  exact congrArg Subtype.val hαβ

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FieldMinimalPicardHull
