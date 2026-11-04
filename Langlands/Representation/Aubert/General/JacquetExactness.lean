import Langlands.Representation.Aubert.General.JacquetCutDiagram
import Langlands.Representation.Aubert.General.StandardExactness
import Langlands.Representation.Aubert.General.SupportCategoryStatements
import Mathlib.Algebra.Exact.Basic

/-! Exactness transport and support reflection for the actual general complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)

/-- Bundle the actual homogeneous Jacquet comparison with its normalized action. -/
def jacquetDegreeRepresentationEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ) :
    ((jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A k)).representation.Equiv
        (jacquetDegreeRepresentation P M U h hclosed hδ hP hU A I k) :=
  Representation.Equiv.mk (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k)
    (fun m => LinearMap.ext
      (jacquetDegreeEquiv_intertwining P M U h hclosed hδ hP hU A I k m))

/-- Injectivity is invariant under the actual homogeneous Jacquet comparison. -/
theorem jacquetDifferential_injective_iff
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (k : ℕ) :
    Function.Injective (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
      (degreeMorphism P M U h hclosed hδ hP hU A k))) ↔
      Function.Injective
        ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k) := by
  constructor
  · intro hf x y hxy
    apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).symm.injective
    apply hf
    apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)).injective
    simpa only [jacquetDegreeEquiv_differential, LinearEquiv.apply_symm_apply] using hxy
  · intro hg x y hxy
    apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).injective
    apply hg
    rw [← jacquetDegreeEquiv_differential, ← jacquetDegreeEquiv_differential, hxy]

/-- Middle exactness is invariant under the actual homogeneous Jacquet comparison. -/
theorem jacquetDifferential_exact_iff
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (k : ℕ) :
    LinearMap.range (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
        (degreeMorphism P M U h hclosed hδ hP hU A k))).toLinearMap =
      LinearMap.ker (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
        (degreeMorphism P M U h hclosed hδ hP hU A (k + 1)))).toLinearMap ↔
      LinearMap.range
          ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k) =
        LinearMap.ker
          ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential (k + 1)) := by
  have he := LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
      (degreeMorphism P M U h hclosed hδ hP hU A k))).toLinearMap
    (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
      (degreeMorphism P M U h hclosed hδ hP hU A (k + 1)))).toLinearMap
    ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k)
    ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential (k + 1))
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).toLinearMap
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)).toLinearMap
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1 + 1)).toLinearMap
    (LinearMap.ext fun x =>
      (jacquetDegreeEquiv_differential P M U h hclosed hδ hP hU A I k x).symm)
    (LinearMap.ext fun x =>
      (jacquetDegreeEquiv_differential P M U h hclosed hδ hP hU A I (k + 1) x).symm)
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).surjective
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)).bijective
    (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1 + 1)).injective
  constructor
  · intro hex
    exact (LinearMap.exact_iff.mp (he.mp (LinearMap.exact_iff.mpr hex.symm))).symm
  · intro hex
    exact (LinearMap.exact_iff.mp (he.mpr (LinearMap.exact_iff.mpr hex.symm))).symm

variable
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Conditional reflection from every associated actual Jacquet diagram.
The support and detection premises are independent of the diagram hypotheses. -/
theorem isExactBeforeTerminal_of_jacquet
    (hdetect : SupportCategoryExactnessDetectionTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (hdegree : ∀ k, k < Complex.terminalDegree I →
      IsInSupportCategory.{uI, uG, max uI uV}
        P M U h hclosed IsAssociate I (hM I) (hL I)
        (StandardComplex.degreeObject P M U h hclosed A k))
    (hinj : 0 < Complex.terminalDegree I →
      ∀ (J : Finset ι) (n : G), IsAssociate I J n →
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
        Function.Injective
          ((jacquetDiagram P M U h hclosed hδ hP hU A J).degreeDifferential 0))
    (hex : ∀ k, k + 1 < Complex.terminalDegree I →
      ∀ (J : Finset ι) (n : G), IsAssociate I J n →
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
        LinearMap.range
            ((jacquetDiagram P M U h hclosed hδ hP hU A J).degreeDifferential k) =
          LinearMap.ker
            ((jacquetDiagram P M U h hclosed hδ hP hU A J).degreeDifferential (k + 1))) :
    StandardComplex.IsExactBeforeTerminal P M U h hclosed hδ hP hU A I := by
  intro k hk
  cases k with
  | zero =>
    let B := StandardComplex.degreeObject P M U h hclosed A 0
    let g := degreeMorphism P M U h hclosed hδ hP hU A 0
    have he : Function.Exact (SmoothRep.hom (0 : B ⟶ B)) (SmoothRep.hom g) := by
      apply (hdetect I (0 : B ⟶ B) g (hdegree 0 hk)).mpr
      intro J n hn hconj
      have hz : (SmoothRep.hom ((jacquetFunctor (h J) (hclosed J)).map
          (0 : B ⟶ B))).toLinearMap = 0 := by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective B.representation (U J) 1 x
        change Jacquet.Localization.mk B.representation (U J) 1 0 = 0
        exact map_zero _
      apply LinearMap.exact_iff.mpr
      rw [hz, LinearMap.range_zero]
      exact LinearMap.ker_eq_bot.mpr
        ((jacquetDifferential_injective_iff P M U h hclosed hδ hP hU A J 0).mpr
          (hinj hk J n hn hconj))
    have he' := LinearMap.exact_iff.mp he
    have hz0 : (SmoothRep.hom (0 : B ⟶ B)).toLinearMap = 0 := rfl
    rw [hz0, LinearMap.range_zero] at he'
    exact he'
  | succ k =>
    have he : Function.Exact
        (SmoothRep.hom (degreeMorphism P M U h hclosed hδ hP hU A k))
        (SmoothRep.hom (degreeMorphism P M U h hclosed hδ hP hU A (k + 1))) := by
      apply (hdetect I _ _ (hdegree (k + 1) hk)).mpr
      intro J n hn hconj
      apply LinearMap.exact_iff.mpr
      exact ((jacquetDifferential_exact_iff P M U h hclosed hδ hP hU A J k).mpr
        (hex k hk J n hn hconj)).symm
    exact LinearMap.exact_iff.mp he

end Langlands.Aubert.General.JacquetComplex
