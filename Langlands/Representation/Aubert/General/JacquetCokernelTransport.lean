import Langlands.Representation.Aubert.General.TerminalCokernelTransport
import Langlands.Representation.Aubert.General.LeviComplex

/-! The natural actual terminal-cokernel bridge for Jacquet and conjugation. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uH uV

section JacquetExactness

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G}

/-- The published full-smooth Jacquet exactness in the generic transport format. -/
theorem jacquetFunctor_mapsShortExactIntertwiners
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Derivative.Mirabolic.MapsShortExactIntertwiners (jacquetFunctor.{uG, uV} h hU) := by
  intro A B C f g hf hg hex
  obtain ⟨h1, h2, h3⟩ := jacquetFunctor_map_isShortExact h hU hUc f g ⟨hf, hg, hex⟩
  exact ⟨h1, h3, h2⟩

end JacquetExactness

namespace StandardComplex

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Monotone P) (hU : Antitone U)

/-- The homogeneous functor in the original standard-subset convention. -/
abbrev degreeFunctor (k : ℕ) :=
  Complex.degreeFunctor.{uI, uG, uV} (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (removedFamily_antitone hP) (removedFamily_monotone hU) k

/-- The incoming natural differential for the complement-reindexed complex. -/
abbrev incomingDifferentialNat (k : ℕ) :=
  Complex.incomingDifferentialNat.{uI, uG, uV}
    (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (removedFamily_antitone hP) (removedFamily_monotone hU) k

/-- The actual natural projection onto the retained standard terminal quotient. -/
abbrev sharpProjectionNat (I : Finset ι) :=
  Complex.terminalProjectionNat.{uI, uG, uV}
    (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (removedFamily_antitone hP) (removedFamily_monotone hU)
    (Complex.terminalDegree I)

variable {H : Type uH} [Group H] [TopologicalSpace H]
variable (J : SmoothRep.{0, uG, max uI uG uV} ℂ G ⥤
  SmoothRep.{0, uH, max uI uG uV} ℂ H)
variable (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

/-- Exact transport of the literal retained standard-complex quotient. -/
def sharpCokernelIso (I : Finset ι) :
    SmoothNatCokernel.functor (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU
        (Complex.terminalDegree I)) J) ≅
      sharpFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU I ⋙ J :=
  Complex.terminalCokernelIso
    (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (removedFamily_antitone hP) (removedFamily_monotone hU)
    J hJ (Complex.terminalDegree I)

/-- Compatibility with the original natural sharp projection. -/
theorem sharpCokernelIso_projection_nat (I : Finset ι) :
    SmoothNatCokernel.projection (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU
        (Complex.terminalDegree I)) J) ≫
      (sharpCokernelIso P M U h hclosed hδ hP hU J hJ I).hom =
        Functor.whiskerRight (sharpProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU I) J :=
  Complex.terminalCokernelIso_projection_nat
    (removedFamily P) (removedFamily M) (removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (removedFamily_antitone hP) (removedFamily_monotone hU)
    J hJ (Complex.terminalDegree I)

/-- Actual normalized Jacquet restriction of sharp is the natural cokernel
of the actual mapped incoming signed differential. -/
def jacquetSharpCokernelIso (I : Finset ι)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U I)) :
    SmoothNatCokernel.functor (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU
        (Complex.terminalDegree I))
      (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I))) ≅
      sharpFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU I ⋙
        jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I) :=
  sharpCokernelIso P M U h hclosed hδ hP hU _
    (jacquetFunctor_mapsShortExactIntertwiners (h I) (hclosed I) hUc) I

/-- The Jacquet comparison retains the mapped canonical sharp projection. -/
theorem jacquetSharpCokernelIso_projection_nat (I : Finset ι)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U I)) :
    SmoothNatCokernel.projection (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU
        (Complex.terminalDegree I))
      (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I))) ≫
      (jacquetSharpCokernelIso P M U h hclosed hδ hP hU I hUc).hom =
        Functor.whiskerRight (sharpProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU I)
          (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)) :=
  sharpCokernelIso_projection_nat P M U h hclosed hδ hP hU _
    (jacquetFunctor_mapsShortExactIntertwiners (h I) (hclosed I) hUc) I

end StandardComplex

end Langlands.Aubert.General
