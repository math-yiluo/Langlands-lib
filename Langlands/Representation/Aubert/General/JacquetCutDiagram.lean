import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Aubert.FiniteProductCoinvariants

/-! The actual normalized Jacquet image of the general standard complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

open CategoryTheory
open scoped BigOperators

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)

/-- The published standard complex, indexed by removed roots. -/
abbrev diagram (A : SmoothRep.{0, uG, max uG uV} ℂ G) : CutComplex.Diagram ι :=
  Complex.diagram (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
    (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
    (fun s => hclosed (Finset.univ \ s)) (fun s => hδ (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone hP) (StandardComplex.removedFamily_monotone hU) A

/-- Apply the actual normalized Jacquet functor to every term and transition. -/
def jacquetDiagram (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) :
    CutComplex.Diagram ι where
  Obj s := (jacquetFunctor (h I) (hclosed I)).obj (CorrectedFiltration.term P M U h hclosed A s)
  add _ := inferInstance
  module _ := inferInstance
  map hst := (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
    (CorrectedFiltration.transition P M U h hclosed hδ hP hU A hst))).toLinearMap
  map_refl s := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
      (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1 x
    change Jacquet.Localization.mk _ (U I) 1
      ((diagram P M U h hclosed hδ hP hU A).map Finset.Subset.rfl v) =
      Jacquet.Localization.mk _ (U I) 1 v
    rw [(diagram P M U h hclosed hδ hP hU A).map_refl]
    rfl
  map_comp {s t u} hst htu := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
      (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1 x
    change Jacquet.Localization.mk _ (U I) 1
      ((diagram P M U h hclosed hδ hP hU A).map htu
        ((diagram P M U h hclosed hδ hP hU A).map hst v)) =
      Jacquet.Localization.mk _ (U I) 1
        ((diagram P M U h hclosed hδ hP hU A).map (hst.trans htu) v)
    rw [(diagram P M U h hclosed hδ hP hU A).map_map]

@[simp] theorem jacquetDiagram_map_mk (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) {s t : Finset ι} (hst : s ⊆ t)
    (v : CorrectedFiltration.term P M U h hclosed A s) :
    (jacquetDiagram P M U h hclosed hδ hP hU A I).map hst
        (Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A s).representation
          (U I) 1 v) =
      Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A t).representation
        (U I) 1 ((diagram P M U h hclosed hδ hP hU A).map hst v) := rfl

/-- The coordinate quotient maps on total families. -/
def totalQuotient (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) :
    (diagram P M U h hclosed hδ hP hU A).Total →ₗ[ℂ]
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Total :=
  LinearMap.piMap (fun s =>
    Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1)

@[simp] theorem totalQuotient_apply (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (x : (diagram P M U h hclosed hδ hP hU A).Total) (s : Finset ι) :
    totalQuotient P M U h hclosed hδ hP hU A I x s =
      Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A s).representation
        (U I) 1 (x s) := rfl

/-- The coordinate quotient maps on homogeneous families. -/
def degreeQuotient (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (k : ℕ) :
    (diagram P M U h hclosed hδ hP hU A).Degree k →ₗ[ℂ]
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree k :=
  LinearMap.piMap (fun s =>
    Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A s.1).representation (U I) 1)

@[simp] theorem degreeQuotient_apply (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Degree k)
    (s : {s : Finset ι // s.card = k}) :
    degreeQuotient P M U h hclosed hδ hP hU A I k x s =
      Jacquet.Localization.mk (CorrectedFiltration.term P M U h hclosed A s.1).representation
        (U I) 1 (x s) := rfl

theorem totalQuotient_extend (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Degree k) :
    totalQuotient P M U h hclosed hδ hP hU A I
        ((diagram P M U h hclosed hδ hP hU A).extend k x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).extend k
        (degreeQuotient P M U h hclosed hδ hP hU A I k x) := by
  funext s
  by_cases hs : s.card = k
  · simp only [totalQuotient_apply, CutComplex.Diagram.extend_apply,
      hs, ↓reduceDIte, degreeQuotient_apply]
  · simp only [totalQuotient_apply, CutComplex.Diagram.extend_apply,
      hs, ↓reduceDIte]
    exact (Jacquet.Localization.mk
      (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1).map_zero

theorem degreeQuotient_restrict (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Total) :
    degreeQuotient P M U h hclosed hδ hP hU A I k
        ((diagram P M U h hclosed hδ hP hU A).restrict k x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).restrict k
        (totalQuotient P M U h hclosed hδ hP hU A I x) := rfl

/-- Every signed insertion commutes with the actual coordinate quotient. -/
theorem totalQuotient_step (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (i : ι) (x : (diagram P M U h hclosed hδ hP hU A).Total) :
    totalQuotient P M U h hclosed hδ hP hU A I
        ((diagram P M U h hclosed hδ hP hU A).step i x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).step i
        (totalQuotient P M U h hclosed hδ hP hU A I x) := by
  funext s
  by_cases hi : i ∈ s
  · simp only [totalQuotient_apply, CutComplex.Diagram.step_apply,
      hi, ↓reduceIte]
    exact (Jacquet.Localization.mk
      (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1).map_smul
        (CutComplex.sign s i) ((diagram P M U h hclosed hδ hP hU A).map
          (Finset.erase_subset i s) (x (s.erase i)))
  · simp only [totalQuotient_apply, CutComplex.Diagram.step_apply,
      hi, ↓reduceIte]
    exact (Jacquet.Localization.mk
      (CorrectedFiltration.term P M U h hclosed A s).representation (U I) 1).map_zero

theorem totalQuotient_differential (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (x : (diagram P M U h hclosed hδ hP hU A).Total) :
    totalQuotient P M U h hclosed hδ hP hU A I
        ((diagram P M U h hclosed hδ hP hU A).differential x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).differential
        (totalQuotient P M U h hclosed hδ hP hU A I x) := by
  simp only [CutComplex.Diagram.differential_apply, map_sum, totalQuotient_step]

/-- The actual coordinate quotients preserve the homogeneous exterior signs. -/
theorem degreeQuotient_differential (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Degree k) :
    degreeQuotient P M U h hclosed hδ hP hU A I (k + 1)
        ((diagram P M U h hclosed hδ hP hU A).degreeDifferential k x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k
        (degreeQuotient P M U h hclosed hδ hP hU A I k x) := by
  change degreeQuotient P M U h hclosed hδ hP hU A I (k + 1)
    ((diagram P M U h hclosed hδ hP hU A).restrict (k + 1)
      ((diagram P M U h hclosed hδ hP hU A).differential
        ((diagram P M U h hclosed hδ hP hU A).extend k x))) = _
  rw [degreeQuotient_restrict, totalQuotient_differential, totalQuotient_extend]
  rfl

/-- Jacquet of the homogeneous finite product is the homogeneous Jacquet diagram. -/
def jacquetDegreeEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (k : ℕ) :
    (jacquetFunctor (h I) (hclosed I)).obj
        (StandardComplex.degreeObject P M U h hclosed A k) ≃ₗ[ℂ]
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree k :=
  (Jacquet.Localization.trivialEquiv
    (StandardComplex.degreeObject P M U h hclosed A k).representation
    (U I) (M I) (h I).levi_le_normalizer).toLinearEquiv.trans
    ((FiniteProduct.coinvariantsEquiv
      (fun s : {s : Finset ι // s.card = k} =>
        (CorrectedFiltration.term P M U h hclosed A s.1).representation) (U I)).trans
      (LinearEquiv.piCongrRight fun s =>
        (Jacquet.Localization.trivialEquiv
          (CorrectedFiltration.term P M U h hclosed A s.1).representation
          (U I) (M I) (h I).levi_le_normalizer).toLinearEquiv.symm))

@[simp] theorem jacquetDegreeEquiv_mk (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Degree k) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k
        (Jacquet.Localization.mk
          (StandardComplex.degreeObject P M U h hclosed A k).representation (U I) 1 x) =
      degreeQuotient P M U h hclosed hδ hP hU A I k x := by
  funext s
  change (Jacquet.Localization.trivialEquiv
    (CorrectedFiltration.term P M U h hclosed A s.1).representation
    (U I) (M I) (h I).levi_le_normalizer).toLinearEquiv.symm
      (Jacquet.mk (CorrectedFiltration.term P M U h hclosed A s.1).representation (U I) (x s)) = _
  rw [← Jacquet.Localization.trivialEquiv_mk]
  exact LinearEquiv.symm_apply_apply _ _

/-- The coordinatewise normalized Levi action on homogeneous Jacquet families. -/
def jacquetDegreeRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ) :
    Representation ℂ (M I) ((jacquetDiagram P M U h hclosed hδ hP hU A I).Degree k) :=
  FiniteProduct.representation (fun s =>
    ((jacquetFunctor (h I) (hclosed I)).obj
      (CorrectedFiltration.term P M U h hclosed A s.1)).representation)

/-- The finite-product comparison respects the actual normalized Levi action. -/
theorem jacquetDegreeEquiv_intertwining (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ) (m : M I)
    (x : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A k)) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k
        (((jacquetFunctor (h I) (hclosed I)).obj
          (StandardComplex.degreeObject P M U h hclosed A k)).representation m x) =
      jacquetDegreeRepresentation P M U h hclosed hδ hP hU A I k m
        (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k x) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    (StandardComplex.degreeObject P M U h hclosed A k).representation (U I) 1 x
  let c : ℂ := ((HaarModulus.closedInverseHalfCharacter (U I) (hclosed I) (M I)
    (h I).levi_le_normalizer m : ℂˣ) : ℂ)
  refine ((jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).map_smul c
    (Jacquet.Localization.mk
      (StandardComplex.degreeObject P M U h hclosed A k).representation (U I) 1
      ((StandardComplex.degreeObject P M U h hclosed A k).representation m v))).trans ?_
  rw [jacquetDegreeEquiv_mk, jacquetDegreeEquiv_mk]
  funext s
  rfl

/-- The literal signed differential as a morphism in the full smooth category. -/
abbrev degreeMorphism (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Complex.degreeMorphism (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
    (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
    (fun s => hclosed (Finset.univ \ s)) (fun s => hδ (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone hP) (StandardComplex.removedFamily_monotone hU) A k

/-- The degree comparison intertwines the actual normalized Jacquet differential. -/
theorem jacquetDegreeEquiv_differential (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (k : ℕ)
    (x : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A k)) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)
        (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
          (degreeMorphism P M U h hclosed hδ hP hU A k)) x) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k
        (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k x) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    (StandardComplex.degreeObject P M U h hclosed A k).representation (U I) 1 x
  change jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)
    (Jacquet.Localization.mk
      (StandardComplex.degreeObject P M U h hclosed A (k + 1)).representation (U I) 1
      ((diagram P M U h hclosed hδ hP hU A).degreeDifferential k v)) = _
  rw [jacquetDegreeEquiv_mk, jacquetDegreeEquiv_mk]
  exact degreeQuotient_differential P M U h hclosed hδ hP hU A I k v

end Langlands.Aubert.General.JacquetComplex
