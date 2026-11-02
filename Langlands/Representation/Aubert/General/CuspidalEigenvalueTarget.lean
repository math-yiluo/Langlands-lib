import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Smooth.IrreducibleRealization
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! # Cuspidal eigenvalue target for the general unadjusted Aubert operator -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]

/-- Vanishing of every proper standard normalized Jacquet module of an actual
smooth representation. On irreducible representations this is Aubert's
cuspidality convention immediately before Notation 1.6. Irreducibility is a
separate hypothesis; no admissibility condition is built into this predicate. -/
def IsStandardCuspidal
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  ∀ I : Finset ι, I ≠ Finset.univ →
    Limits.IsZero ((jacquetFunctor (h I) (hU I)).obj A)

/-- Aubert Theorem 1.7(4): an actual irreducible cuspidal representation has
eigenvalue `(-1)^|S|` for the unadjusted alternating operator. Its class uses
the published finite-length theorem for an irreducible representation. -/
def CuspidalEigenvalueStatement
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I)) : Prop :=
  ∀ (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.IsIrreducible),
    IsStandardCuspidal P M U h hU A →
      alternatingOperator P M U h hU hfl
          (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA)) =
        ((-1 : ℤ) ^ Fintype.card ι) •
          SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA)

end Langlands.Aubert.General
