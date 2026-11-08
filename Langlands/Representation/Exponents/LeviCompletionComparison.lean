import Langlands.Representation.Jacquet.FixedCompletionComparison
import Langlands.Representation.Exponents.LeviJacquetCompletionTransport
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups

/-!
# The represented-parabolic completion comparison from compression data

The actual Levi-point and normalization transports are assembled with the
fixed-completion Jacquet equivalence. The contraction basis, stationary images
and pointwise Jacquet bijections remain explicit inputs.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance ambientComparisonPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

omit [T2Space k] in
/-- Each radical point belongs to an actual compact subgroup of the ambient group. -/
theorem pointImage_radical_compact_cover (p : P ⟶ G) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    ∀ x ∈ pointImage (n ≫ p), ∃ C : Subgroup (rationalPoints G),
      IsCompact (C : Set (rationalPoints G)) ∧ C ≤ pointImage (n ≫ p) ∧ x ∈ C := by
  intro x hx
  obtain ⟨C, hC, hsub⟩ :=
    isLimitOfCompactSubgroups_pointImage_radical p n hp.isClosedSubgroup hn.1
      {⟨x, hx⟩} (isCompact_singleton)
  refine ⟨C.map (pointImage (n ≫ p)).subtype, ?_, ?_, ?_⟩
  · exact hC.image continuous_subtype_val
  · rintro y ⟨z, _, rfl⟩
    exact z.property
  · exact ⟨⟨x, hx⟩, hsub (Set.mem_singleton _), rfl⟩

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
variable (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
variable (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
  (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
  (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
  (hmulbar : IsIso (subgroupMultiplication mbar nbar))
variable (hLevi : mbar ≫ pbar = m ≫ p)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
include hLevi hn in
/-- The second realization of the same Levi normalizes the first radical. -/
theorem pointImage_opposite_levi_le_normalizer :
    pointImage (mbar ≫ pbar) ≤ Subgroup.normalizer (pointImage (n ≫ p)) := by
  rw [hLevi]
  exact pointImage_le_normalizer p m n hn

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- An actual Levi compact index with the specified ambient image is the
intersection index transported through the actual Levi-point isomorphism. -/
theorem leviCompactIndex_transport_eq
    (K : CompactOpenSubgroup (rationalPoints G)) :
    letI := leviPointTopology mbar hmbar
    ∀ KM : CompactOpenSubgroup (rationalPoints M),
      (∀ y, y ∈ KM.1 ↔ (leviPointsEquiv pbar mbar hpbar hmbar y :
        rationalPoints G) ∈ K.1) →
      CompactCompletion.compactIndexComap (leviPointsEquiv pbar mbar hpbar hmbar).symm KM =
        Jacquet.leviCompactIndex (pointImage (mbar ≫ pbar))
          (isClosed_leviPoints pbar mbar hpbar hmbar) K := by
  let := leviPointTopology mbar hmbar
  intro KM hKM
  apply Subtype.ext
  apply OpenSubgroup.ext
  intro z
  change (leviPointsEquiv pbar mbar hpbar hmbar).symm z ∈ KM.1 ↔
    (z : rationalPoints G) ∈ K.1
  rw [hKM, (leviPointsEquiv pbar mbar hpbar hmbar).apply_symm_apply]

variable (g : rationalPoints G)
  (hcentral : ∀ a ∈ pointImage (mbar ≫ pbar), a * g = g * a)
  (hBasis : Jacquet.HasOppositeIwahoriContractionBasis
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g)
variable (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hstationary : ∀ K ∈ Jacquet.oppositeCompressionIndices
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g,
    ∃ b : ℕ, Jacquet.stableImage π.representation π.isSmooth K.1 K.2 g =
      LinearMap.range (Jacquet.compressedAction π.representation π.isSmooth K.1 K.2 g ^ b))
  (hbij : ∀ K : Jacquet.oppositeCompressionIndices
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g,
    Function.Bijective (Jacquet.stableImageJacquetMap π.representation π.isSmooth
      K.1.1 K.1.2 g (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar))
      (pointImage_le_normalizer pbar mbar nbar hnbar)))

/-- Conditional completion comparison for the actual represented functor. -/
def leviCompletionComparisonEquiv :
    letI := leviPointTopology mbar hmbar
    haveI := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
    CompactCompletion.completionFixed π.representation π.isSmooth (pointImage (n ≫ p)) ≃ₗ[ℂ]
      CompactCompletion.completion
        ((leviJacquetFunctor pbar mbar nbar hpbar hnbar hmbar hmulbar).obj π).representation
        ((leviJacquetFunctor pbar mbar nbar hpbar hnbar hmbar hmulbar).obj π).isSmooth := by
  letI := leviPointTopology mbar hmbar
  haveI := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
  exact (Jacquet.fixedCompletionJacquetEquiv
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g
    π.representation π.isSmooth (pointImage_le_normalizer pbar mbar nbar hnbar)
    (pointImage_opposite_levi_le_normalizer p m n hn pbar mbar hLevi) hcentral
    (isClosed_leviPoints pbar mbar hpbar hmbar)
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
    hBasis (pointImage_radical_compact_cover p n hp hn) hstationary hbij).trans
      (leviJacquetCompletionTransportEquiv pbar mbar nbar hpbar hnbar hmbar hmulbar π)

/-- The component formula at every factorization index, independently of the
contracting element chosen to build the equivalence. -/
theorem leviCompletionComparisonEquiv_apply_of_factor :
    letI := leviPointTopology mbar hmbar
    haveI := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
    ∀ (x : CompactCompletion.completionFixed π.representation π.isSmooth
        (pointImage (n ≫ p))) (K : CompactOpenSubgroup (rationalPoints G)),
      (∀ k ∈ K.1, ∃ l ∈ K.1.toSubgroup ⊓ pointImage (n ≫ p),
        ∃ z ∈ K.1.toSubgroup ⊓ pointImage (mbar ≫ pbar),
        ∃ u ∈ K.1.toSubgroup ⊓ pointImage (nbar ≫ pbar), k = l * z * u) →
      ∀ KM : CompactOpenSubgroup (rationalPoints M),
        (∀ y, y ∈ KM.1 ↔ (leviPointsEquiv pbar mbar hpbar hmbar y :
          rationalPoints G) ∈ K.1) →
        (leviCompletionComparisonEquiv p m n hp hn pbar mbar nbar hpbar hmbar
          hnbar hmulbar hLevi g hcentral hBasis π hstationary hbij x).val KM =
            Jacquet.Localization.mk π.representation (pointImage (nbar ≫ pbar)) 1
              (x.val.val K) := by
  let := leviPointTopology mbar hmbar
  have := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
  intro x K hfactor KM hKM
  change (leviJacquetCompletionTransportEquiv pbar mbar nbar hpbar hnbar hmbar hmulbar π
    (Jacquet.fixedCompletionJacquetEquiv
      (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g
      π.representation π.isSmooth (pointImage_le_normalizer pbar mbar nbar hnbar)
      (pointImage_opposite_levi_le_normalizer p m n hn pbar mbar hLevi) hcentral
      (isClosed_leviPoints pbar mbar hpbar hmbar)
      (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
      hBasis (pointImage_radical_compact_cover p n hp hn) hstationary hbij x)).val KM = _
  rw [leviJacquetCompletionTransportEquiv_apply,
    leviCompactIndex_transport_eq pbar mbar hpbar hmbar K KM hKM,
    Jacquet.fixedCompletionJacquetEquiv_apply_of_factor
      (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g
      π.representation π.isSmooth (pointImage_le_normalizer pbar mbar nbar hnbar)
      (pointImage_opposite_levi_le_normalizer p m n hn pbar mbar hLevi) hcentral
      (isClosed_leviPoints pbar mbar hpbar hmbar)
      (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
      hBasis (pointImage_radical_compact_cover p n hp hn) hstationary hbij x K hfactor,
    leviJacquetCompletionTransport_trivialEquiv_symm_mk pbar mbar nbar hnbar π]

variable (σ : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hstationaryσ : ∀ K ∈ Jacquet.oppositeCompressionIndices
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g,
    ∃ b : ℕ, Jacquet.stableImage σ.representation σ.isSmooth K.1 K.2 g =
      LinearMap.range (Jacquet.compressedAction σ.representation σ.isSmooth K.1 K.2 g ^ b))
  (hbijσ : ∀ K : Jacquet.oppositeCompressionIndices
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g,
    Function.Bijective (Jacquet.stableImageJacquetMap σ.representation σ.isSmooth
      K.1.1 K.1.2 g (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar))
      (pointImage_le_normalizer pbar mbar nbar hnbar)))

/-- The comparison is natural for the actual normalized Jacquet functor. -/
theorem leviCompletionComparisonEquiv_natural (f : π ⟶ σ) :
    letI := leviPointTopology mbar hmbar
    haveI := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
    ∀ (x : CompactCompletion.completionFixed π.representation π.isSmooth
        (pointImage (n ≫ p)))
      (y : CompactCompletion.completionFixed σ.representation σ.isSmooth
        (pointImage (n ≫ p))),
      (∀ K : CompactOpenSubgroup (rationalPoints G),
        y.val.val K = SmoothRep.hom f (x.val.val K)) →
      ∀ KM : CompactOpenSubgroup (rationalPoints M),
        (leviCompletionComparisonEquiv p m n hp hn pbar mbar nbar hpbar hmbar
          hnbar hmulbar hLevi g hcentral hBasis σ hstationaryσ hbijσ y).val KM =
            SmoothRep.hom ((leviJacquetFunctor pbar mbar nbar hpbar hnbar hmbar hmulbar).map f)
              ((leviCompletionComparisonEquiv p m n hp hn pbar mbar nbar hpbar hmbar
                hnbar hmulbar hLevi g hcentral hBasis π hstationary hbij x).val KM) := by
  let := leviPointTopology mbar hmbar
  have := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
  intro x y hxy KM
  apply leviJacquetCompletionTransportEquiv_natural pbar mbar nbar hpbar hnbar hmbar hmulbar
    π σ f _ _ _ KM
  intro J
  exact Jacquet.fixedCompletionJacquetEquiv_natural
    (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g
    π.representation π.isSmooth (pointImage_le_normalizer pbar mbar nbar hnbar)
    (pointImage_opposite_levi_le_normalizer p m n hn pbar mbar hLevi) hcentral
    (isClosed_leviPoints pbar mbar hpbar hmbar)
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
    hBasis (pointImage_radical_compact_cover p n hp hn) hstationary hbij
    σ.representation σ.isSmooth hstationaryσ hbijσ (SmoothRep.hom f) x y hxy J

end Langlands.Aubert.General.RepresentedParabolic
