import Langlands.Representation.Geometric.GrothendieckProof
import Langlands.Representation.Geometric.InducedPieceGrothendieck
import Langlands.Representation.Aubert.QuasicuspidalEigenvalue
import Langlands.Representation.CuspidalSupport.JacquetExactnessReflection
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Aubert.FiniteProductGrothendieck

/-! Actual constituent support of induction after Jacquet on quasicuspidal induction. -/

noncomputable section

namespace Langlands.Aubert.QuasicuspidalCutSupport

open CategoryTheory GeneralLinear Geometric Parabolic SmoothRep CuspidalSupport
open SmoothRep.IrreducibleGrothendieckProof
open CuspidalSupport.MinimalRefinedJacquet
open scoped BigOperators Classical

universe uF uV uG

set_option maxHeartbeats 1000000

private theorem support_of_subquotient
    {G : Type uG} [Group G] [TopologicalSpace G]
    {A D I : SmoothRep.{0,uG,uV} ℂ G}
    (hA : HasConstituentSupportIn A I) (hD : IsSubquotient D A) :
    HasConstituentSupportIn D I := by
  intro S hS hSD
  exact hA S hS (smoothSubquotientTransitivity ℂ G A D S hSD hD)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n)

/-- Every nonzero subquotient of every actual degree is detected by the
normalized Jacquet functors at Levis associated to `B`. -/
def DegreesDetected :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun π => ∀ k, JacquetReflection.DetectsSubquotients.{uF,max uF uV} F T
    (LevisAssociated (F := F.Carrier) B)
    (ActualCutComplex.degreeObject T π.representation k)

/-- An induced geometric piece has zero class or the original induced class,
according as the source refinement is proper or whole. -/
theorem inducedGeometricPieceK0_quasicuspidal
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength), IsLeviQuasicuspidal B A.representation →
      normalizedInductionK0.{uF,uV} F T C
          (geometricPieceK0.{uF,uV} F T B C w S R hS hR
            (B.finiteLengthClass F.Carrier A hA)) =
        if S = wholeRefinement B then
          normalizedInductionK0.{uF,uV} F T B
            (B.finiteLengthClass F.Carrier A hA) else 0 := by
  let := T.topology
  intro A hA hqc
  classical
  have hp := LinearMap.congr_fun
    (normalizedInductionK0_comp_geometricPieceK0.{uF,uV} F T B C w S R hS hR)
    (B.finiteLengthClass F.Carrier A hA)
  change normalizedInductionK0 F T C
      (geometricPieceK0 F T B C w S R hS hR
        (B.finiteLengthClass F.Carrier A hA)) =
    normalizedInductionK0 F T B
      (normalizedRefinedInductionK0 F T B S
        (normalizedRefinedJacquetK0 F T B S
          (B.finiteLengthClass F.Carrier A hA))) at hp
  rw [hp]
  split_ifs with hs
  · subst S
    have hw := LinearMap.congr_fun
      (refinedInductionJacquetK0_wholeRefinement.{uF,uV} F T B)
      (B.finiteLengthClass F.Carrier A hA)
    change normalizedRefinedInductionK0 F T B (wholeRefinement B)
        (normalizedRefinedJacquetK0 F T B (wholeRefinement B)
          (B.finiteLengthClass F.Carrier A hA)) =
      B.finiteLengthClass F.Carrier A hA at hw
    rw [hw]
  · have hproper : refinedParabolic F.Carrier B S ≠ ⊤ := by
      intro hfull
      exact hs (eq_wholeRefinement_of_refinedParabolic_eq_top B S hfull)
    rw [normalizedRefinedJacquetK0_quasicuspidal F T B S A hA hqc hproper,
      map_zero, map_zero]

/-- The actual geometric filtration gives a natural multiple in exact K0.
No splitting of the actual representation is asserted. -/
theorem inductionJacquetInduction_natural_multiple (hn : 0 < n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength), IsLeviQuasicuspidal B A.representation →
      ∃ N : ℕ, normalizedInductionK0.{uF,uV} F T C
          (normalizedJacquetK0.{uF,uV} F T C
            (normalizedInductionK0.{uF,uV} F T B
              (B.finiteLengthClass F.Carrier A hA))) =
        N • normalizedInductionK0.{uF,uV} F T B
          (B.finiteLengthClass F.Carrier A hA) := by
  let := T.topology
  intro A hA hqc
  classical
  obtain ⟨S, R, hS, hR, m, e, hg⟩ :=
    geometricLemmaGrothendieck.{uF,uV} F T n hn B C
  obtain ⟨hP, hclass⟩ := hg A hA
  refine ⟨∑ i : Fin m, if S (e i) = wholeRefinement B then 1 else 0, ?_⟩
  rw [hclass, map_sum]
  trans ∑ i : Fin m, (if S (e i) = wholeRefinement B then 1 else 0 : ℕ) •
    normalizedInductionK0.{uF,uV} F T B (B.finiteLengthClass F.Carrier A hA)
  · apply Finset.sum_congr rfl
    intro i _
    rw [← geometricPieceK0_finiteLengthClass.{uF,uV} F T B C (e i).val
      (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1 A hA (hP i)]
    rw [inducedGeometricPieceK0_quasicuspidal F T B C (e i).val
      (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1 A hA hqc]
    split_ifs <;> simp
  · rw [Finset.sum_smul]

/-- Applying actual normalized induction to an injective/surjective presentation
preserves the actual smooth subquotient relation. -/
theorem normalizedInduction_subquotient :
    letI := T.topology
    ∀ {A D : SmoothRep.{0,uF,uV} ℂ (C.Levi F.Carrier)},
      IsSubquotient D A →
      IsSubquotient ((T.normalizedParabolicInductionFunctor C).obj D)
        ((T.normalizedParabolicInductionFunctor C).obj A) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A D hD
  obtain ⟨X, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hD
  refine isSubquotient_iff_exists.mpr
    ⟨(T.normalizedParabolicInductionFunctor C).obj X,
      (T.normalizedParabolicInductionFunctor C).map i,
      (T.normalizedParabolicInductionFunctor C).map q, ?_, ?_⟩
  · exact T.normalizedParabolicInducedMap_injective C (hom i) hi
  · exact Classification.normalizedParabolicMap_surjective F T C X D (hom q) hq

/-- The actual induction--Jacquet composite preserves actual subquotients. -/
theorem normalizedInductionJacquet_subquotient :
    letI := T.topology
    ∀ {A D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)},
      IsSubquotient D A →
      IsSubquotient
        ((T.normalizedParabolicInductionFunctor C).obj
          ((T.normalizedJacquetFunctor C).obj D))
        ((T.normalizedParabolicInductionFunctor C).obj
          ((T.normalizedJacquetFunctor C).obj A)) := by
  let := T.topology
  intro A D hD
  exact normalizedInduction_subquotient.{uF,max uF uV} F T C
    (normalizedJacquetSubquotient p F T n C A D hD)

/-- All actual irreducible constituents of induction after Jacquet of the
original induction already occur in that original induction. -/
theorem inductionJacquetInduction_constituentSupport (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      HasConstituentSupportIn
        ((T.normalizedParabolicInductionFunctor C).obj
          ((T.normalizedJacquetFunctor C).obj
            ((T.normalizedParabolicInductionFunctor B).obj σ)))
        ((T.normalizedParabolicInductionFunctor B).obj σ) := by
  let := T.topology
  intro σ hσ hqc
  have hI := normalizedInductionK0_hasFiniteLength.{uF,uV} F T B σ hσ
  have hJ := normalizedJacquetK0_hasFiniteLength.{uF,uV} F T C _ hI
  have hIJ := normalizedInductionK0_hasFiniteLength.{uF,uV} F T C _ hJ
  obtain ⟨N, he⟩ := inductionJacquetInduction_natural_multiple F T B C hn σ hσ hqc
  rw [normalizedInductionK0_finiteLengthClass F T B σ hσ hI,
    normalizedJacquetK0_finiteLengthClass F T C _ hI hJ,
    normalizedInductionK0_finiteLengthClass F T C _ hJ hIJ] at he
  exact hasConstituentSupportIn_of_class_natural_multiple
    ⟨_, hIJ⟩ ⟨_, hI⟩ N he

/-- Actual cut terms of every subquotient of the original induction have
irreducible constituent support in that original induction. -/
theorem inductionJacquet_constituentSupport (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        HasConstituentSupportIn
          ((T.normalizedParabolicInductionFunctor C).obj
            ((T.normalizedJacquetFunctor C).obj π))
          ((T.normalizedParabolicInductionFunctor B).obj σ) := by
  let := T.topology
  intro σ hσ hqc π hπ
  exact support_of_subquotient
    (inductionJacquetInduction_constituentSupport F T B C hn σ hσ hqc)
    (normalizedInductionJacquet_subquotient F T C hπ)

/-- Finite length and actual constituent support extend the associated-family
detector from the original induction to every nonzero subquotient of `A`. -/
theorem detects_of_constituentSupport :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
        A.HasFiniteLength →
        HasConstituentSupportIn A ((T.normalizedParabolicInductionFunctor B).obj σ) →
        JacquetReflection.DetectsSubquotients.{uF,max uF uV} F T
          (LevisAssociated (F := F.Carrier) B) A := by
  let := T.topology
  intro σ hqc A hA hsup D hDA hD
  let : Nontrivial D := hD
  obtain ⟨S, hS, hSD⟩ := exists_irreducible_subquotient D
    (hasFiniteLength_of_isSubquotient hA hDA)
  have hSA : IsSubquotient S A := smoothSubquotientTransitivity ℂ _ A D S hSD hDA
  have hSne : Nontrivial S :=
    CuspidalSupport.nontrivial_of_isIrreducible S.representation (hρ := hS)
  obtain ⟨E, hBE, hJS, _⟩ := cuspidalInductionSubquotientJacquet F T n B σ hqc
    S (hsup S hS hSA) hSne
  refine ⟨E, hBE, ?_⟩
  have hJSD := normalizedJacquetSubquotient p F T n E D S hSD
  by_contra hz
  have hDz : Subsingleton ((T.normalizedJacquetFunctor E).obj D) :=
    not_nontrivial_iff_subsingleton.mp hz
  let := hDz
  have hSz := CuspidalSupport.subsingleton_of_isSubquotient hJSD
  exact not_nontrivial_iff_subsingleton.mpr hSz hJS

/-- The actual finite term is the object of the actual composite functors. -/
theorem finiteTerm_val :
    letI := T.topology
    ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.HasFiniteLength),
      (ActualCutComplex.finiteTerm.{uF,uV} F T C π hπ).val =
        (T.normalizedParabolicInductionFunctor C).obj
          ((T.normalizedJacquetFunctor C).obj π) := by
  intros
  rfl

/-- Every actual cut term has constituent support in the original induction. -/
theorem term_constituentSupport (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        HasConstituentSupportIn
          (ActualCutComplex.finiteTerm.{uF,uV} F T C π hπ).val
          ((T.normalizedParabolicInductionFunctor B).obj σ) := by
  let := T.topology
  intro σ hσ hqc π hπ hsub
  rw [finiteTerm_val F T C π hπ]
  exact inductionJacquet_constituentSupport F T B C hn σ hσ hqc π hsub

/-- Every actual cut term is detected by the Levis associated to the inducing
quasicuspidal Levi. -/
theorem term_detectsSubquotients (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        JacquetReflection.DetectsSubquotients.{uF,max uF uV} F T
          (LevisAssociated (F := F.Carrier) B)
          (ActualCutComplex.finiteTerm.{uF,uV} F T C π hπ).val := by
  let := T.topology
  intro σ hσ hqc π hπ hsub
  exact detects_of_constituentSupport F T B σ hqc
    (ActualCutComplex.finiteTerm.{uF,uV} F T C π hπ).val
    (ActualCutComplex.finiteTerm.{uF,uV} F T C π hπ).property
    (term_constituentSupport F T B C hn σ hσ hqc π hπ hsub)

/-- Actual finite-product degrees inherit the same constituent support from
the exact sum of their cut-term classes. -/
theorem degree_constituentSupport (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        ∀ k, HasConstituentSupportIn
          (ActualCutComplex.finiteDegree.{uF,uV} F T π hπ k).val
          ((T.normalizedParabolicInductionFunctor B).obj σ) := by
  let := T.topology
  intro σ hσ hqc π hπ hsub k
  refine hasConstituentSupportIn_of_class_sum
    (ActualCutComplex.finiteDegree.{uF,uV} F T π hπ k)
    ⟨_, normalizedInductionK0_hasFiniteLength.{uF,uV} F T B σ hσ⟩
    (fun s : {s : Finset (Fin (n - 1)) // s.card = k} =>
      ActualCutComplex.finiteTerm.{uF,uV} F T (ActualCutComplex.shape s.1) π hπ) ?_ ?_
  · intro s
    exact term_constituentSupport F T B (ActualCutComplex.shape s.1)
      hn σ hσ hqc π hπ hsub
  · exact ActualCutComplex.degree_class.{uF,uV} F T k π hπ

/-- Every nonzero actual subquotient of every actual cut-complex degree is
detected by a Jacquet module at a Levi associated to the source. -/
theorem degree_detectsSubquotients (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        ∀ k, JacquetReflection.DetectsSubquotients.{uF,max uF uV} F T
          (LevisAssociated (F := F.Carrier) B)
          (ActualCutComplex.finiteDegree.{uF,uV} F T π hπ k).val := by
  let := T.topology
  intro σ hσ hqc π hπ hsub k
  exact detects_of_constituentSupport F T B σ hqc _
    (ActualCutComplex.finiteDegree.{uF,uV} F T π hπ k).property
    (degree_constituentSupport F T B hn σ hσ hqc π hπ hsub k)

/-- Every finite-length subquotient of the original quasicuspidal induction
satisfies the actual all-degree detecting predicate. -/
theorem degreesDetected (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (_hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        DegreesDetected F T B π := by
  let := T.topology
  intro σ hσ hqc π hπ hsub k
  exact degree_detectsSubquotients F T B hn σ hσ hqc π hπ hsub k

end Langlands.Aubert.QuasicuspidalCutSupport
