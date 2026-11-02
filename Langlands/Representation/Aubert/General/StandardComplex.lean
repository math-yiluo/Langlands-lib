import Langlands.Representation.Aubert.General.Initial

/-! The standard-subset dictionary for the removed-root normalized complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.StandardComplex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]

/-- Reindex a standard-subset family by the roots that have been removed. -/
def removedFamily {α : Sort*} (F : Finset ι → α) (s : Finset ι) : α :=
  F (Finset.univ \ s)

/-- Increasing standard parabolics become decreasing in the removed-root index. -/
theorem removedFamily_antitone {α : Type*} [Preorder α] {F : Finset ι → α}
    (hF : Monotone F) : Antitone (removedFamily F) :=
  fun _ _ hst => hF (Finset.sdiff_subset_sdiff_right Finset.univ hst)

/-- Decreasing standard radicals become increasing in the removed-root index. -/
theorem removedFamily_monotone {α : Type*} [Preorder α] {F : Finset ι → α}
    (hF : Antitone F) : Monotone (removedFamily F) :=
  fun _ _ hst => hF (Finset.sdiff_subset_sdiff_right Finset.univ hst)

/-- At the retained degree, complementary standard subsets have cardinality `|I|`. -/
def terminalIndexEquiv (I : Finset ι) :
    {s : Finset ι // s.card = Complex.terminalDegree I} ≃
      {J : Finset ι // J.card = I.card} where
  toFun s := ⟨Finset.univ \ s.1, by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, s.2]
    have hi := Finset.card_le_univ I
    unfold Complex.terminalDegree
    omega⟩
  invFun J := ⟨Finset.univ \ J.1, by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, J.2]
    rfl⟩
  left_inv s := Subtype.ext (Finset.sdiff_sdiff_eq_self (Finset.subset_univ _))
  right_inv J := Subtype.ext (Finset.sdiff_sdiff_eq_self (Finset.subset_univ _))

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
variable (hclosed : ∀ J, IsClosed (U J : Set G))
variable (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
variable (hP : Monotone P) (hU : Antitone U)

/-- The actual homogeneous object, with `s` standing for the removed roots. -/
abbrev degreeObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Complex.degreeObject (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A k

/-- Every coordinate is the genuine normalized standard induction--Jacquet object. -/
theorem termObject_eq (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    Complex.termObject (removedFamily P) (removedFamily M) (removedFamily U)
        (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s =
      (inductionJacquetFunctor.{uG, uV} (h (Finset.univ \ s))
        (hclosed (Finset.univ \ s))).obj A := rfl

/-- The signed differential for the complementary standard-subset family. -/
abbrev differential (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Complex.differential (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) A k

/-- The incoming image submodule in the standard-subset convention. -/
abbrev boundary (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Complex.boundary (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) A k

/-- The canonical equivariant quotient map at any truncation degree. -/
abbrev terminalProjection (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Complex.terminalProjection (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) A k

/-- The retained actual terminal cokernel, with the original support subset `I`. -/
abbrev sharpObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) :=
  Complex.sharpObject (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) A I

/-- The terminal cokernel is natural on the full smooth category. -/
abbrev sharpFunctor (I : Finset ι) :=
  Complex.sharpFunctor (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) I

/-- The canonical map from the input object to removed-root degree zero. -/
abbrev initialMap (A : SmoothRep.{0, uG, max uG uV} ℂ G) :=
  Complex.initialMap (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) A

/-- The initial equivalence uses the full standard-subset endpoints. -/
abbrev initialEquiv (hPtop : P Finset.univ = ⊤) (hUtop : U Finset.univ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :=
  Complex.initialEquiv (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (by simpa only [removedFamily, Finset.sdiff_empty] using hPtop)
    (by simpa only [removedFamily, Finset.sdiff_empty] using hUtop) A

/-- The canonical first arrow from the input smooth representation. -/
abbrev initialDifferential (A : SmoothRep.{0, uG, max uG uV} ℂ G) :=
  Complex.initialDifferential (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s))
    (removedFamily_antitone hP) (removedFamily_monotone hU) A

end Langlands.Aubert.General.StandardComplex
