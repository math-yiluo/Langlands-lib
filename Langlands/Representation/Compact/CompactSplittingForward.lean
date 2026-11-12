import Langlands.Representation.CompactCoefficient.TotalProjector
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.Category.IdempotentDecomposition

/-! # Finite fixed-level compact classes give the category decomposition -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open CategoryTheory CompactCoefficientClass

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]

include μ in
/-- The (KF) direction of Renard IV.1.7, using the actual compact-isotypic projectors. -/
theorem compactCategoryDecomposition_of_finite_strata
    (hKF : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      (fixedStratum.{u, v} K.toSubgroup).Finite) :
    Renard.IsCategoryDecomposition
      (SmoothRep.irreducibleSubquotientProperties
        (fun A : SmoothRep.{0, u, v} ℂ G => HasCompactSmoothDualCoefficients A.representation)) := by
  classical
  have hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  let h : ∀ (c : CompactCoefficientClass.{u, v} G) (A : SmoothRep.{0, u, v} ℂ G),
      IsCompl (isotypicSubrepresentation c A).toSubmodule
        (annihilatorSubrepresentation c A).toSubmodule :=
    CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof
  let e := isotypicProjectorFamilyOfIsCompl h
  have heid (c : CompactCoefficientClass.{u, v} G) (A : SmoothRep.{0, u, v} ℂ G) (x : A) :
      e c A (e c A x) = e c A x :=
    LinearMap.congr_fun (isotypicProjectorOfIsCompl_idempotent c (h c A)) x
  have heorth (c d : CompactCoefficientClass.{u, v} G) (hcd : c ≠ d)
      (A : SmoothRep.{0, u, v} ℂ G) (x : A) : e c A (e d A x) = 0 :=
    congrArg (fun f : A.representation.IntertwiningMap A.representation => f x)
      (isotypicProjectorFamilyOfIsCompl_orthogonal h hcd.symm A)
  have hefinite (A : SmoothRep.{0, u, v} ℂ G) (x : A) :
      Function.HasFiniteSupport (fun c => e c A x) := by
    obtain ⟨L, hx⟩ := A.isSmooth x
    obtain ⟨K, hK, hKL⟩ := hcof L
    apply finiteSupport_of_finite_stratum (fun c => e c A) x (fixedStratum K.toSubgroup) (hKF K hK)
    intro c hc
    apply apply_eq_zero_of_annihilator_le_ker c K.toSubgroup hc (e c A)
      (isotypicProjectorOfIsCompl_ker c (h c A)).symm.le
    intro k
    exact hx ⟨k.val, hKL k.property⟩
  let p := fun A : SmoothRep.{0, u, v} ℂ G => pointwiseFiniteSum (fun c => e c A) (hefinite A)
  have hpid (A : SmoothRep.{0, u, v} ℂ G) (x : A) : p A (p A x) = p A x :=
    pointwiseFiniteSum_idempotent (fun c => e c A) (hefinite A)
      (fun c => heid c A) (fun c d hcd => heorth c d hcd A) x
  have hprange (A : SmoothRep.{0, u, v} ℂ G) :
      (p A).range = totalIsotypicSubrepresentation.{u, v} A := by
    change (pointwiseFiniteSum (fun c => e c A) (hefinite A)).range = _
    rw [pointwiseFiniteSum_range (fun c => e c A) (hefinite A)
      (fun c => heid c A) (fun c d hcd => heorth c d hcd A)]
    exact iSup_congr fun c => isotypicProjectorOfIsCompl_range c (h c A)
  apply SmoothRep.categoryDecomposition_of_natural_idempotent _ p
  · intro A B f x
    exact pointwiseFiniteSum_covariant (fun c => e c A) (hefinite A)
      (fun c => e c B) (hefinite B) (SmoothRep.hom f).toLinearMap (Equiv.refl _)
      (fun c y => (isotypicProjectorOfIsCompl_natural c (h c A) (h c B)
        (SmoothRep.hom f) y).symm) x
  · exact hpid
  · intro D hD
    constructor
    · intro hfix x
      apply totalIsotypicSubrepresentation_le_compactCoefficientVectors D
      rw [← hprange D]
      exact ⟨x, hfix x⟩
    · intro hc x
      have hx : x ∈ (p D).range := by
        rw [hprange, totalIsotypicSubrepresentation_eq_top_of_compactCoefficients μ D hc]
        trivial
      obtain ⟨y, rfl⟩ := hx
      exact hpid D y

end Langlands.Renard.CompactRepresentation
