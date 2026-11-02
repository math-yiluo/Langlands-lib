import Langlands.Representation.Aubert.General.StandardComplex

/-! Exactness before the retained terminal cokernel of the actual smooth complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.StandardComplex

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
variable (hclosed : ∀ J, IsClosed (U J : Set G))
variable (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
variable (hP : Monotone P) (hU : Antitone U)

/-- Exactness at every homogeneous term strictly before the retained terminal degree. -/
def IsExactBeforeTerminal (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) : Prop :=
  ∀ k : ℕ, k < Complex.terminalDegree I →
    LinearMap.ker (differential P M U h hclosed hδ hP hU A k).toLinearMap =
      boundary P M U h hclosed hδ hP hU A k

/-- The final projection is onto the actual quotient, regardless of earlier exactness. -/
theorem terminalProjection_surjective (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (k : ℕ) :
    Function.Surjective (terminalProjection P M U h hclosed hδ hP hU A k) :=
  Complex.terminalProjection_surjective _ _ _ _ _ _ _ _ A k

/-- Exactness at the retained last term is the defining kernel law of its quotient. -/
theorem terminalProjection_ker (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    LinearMap.ker (terminalProjection P M U h hclosed hδ hP hU A k).toLinearMap =
      boundary P M U h hclosed hδ hP hU A k :=
  Complex.terminalProjection_ker _ _ _ _ _ _ _ _ A k

/-- Before a positive terminal degree, the first arrow from the actual input is injective. -/
theorem initialDifferential_injective_of_exact
    (hPtop : P Finset.univ = ⊤) (hUtop : U Finset.univ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (hA : IsExactBeforeTerminal P M U h hclosed hδ hP hU A I)
    (hpos : 0 < Complex.terminalDegree I) :
    Function.Injective (initialDifferential P M U h hclosed hδ hP hU A) := by
  have hker : LinearMap.ker (differential P M U h hclosed hδ hP hU A 0).toLinearMap = ⊥ :=
    hA 0 hpos
  have hd := LinearMap.ker_eq_bot.mp hker
  have hi := (initialEquiv P M U h hclosed hδ hPtop hUtop A).injective
  exact hd.comp hi

/-- When `I` is the full root set there are no earlier terms to require exactness at. -/
theorem isExactBeforeTerminal_univ (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    IsExactBeforeTerminal P M U h hclosed hδ hP hU A Finset.univ := by
  intro k hk
  simp [Complex.terminalDegree] at hk

end Langlands.Aubert.General.StandardComplex
