import Langlands.Representation.Category.NaturalCokernel
import Langlands.Representation.Aubert.General.Naturality

/-! Natural transport of the actual retained terminal cokernel. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.Complex

open CategoryTheory

universe uI uG uH uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Antitone P) (hU : Monotone U)

/-- The incoming signed differential, with the zero map in degree zero. -/
def incomingDifferentialNat (k : ℕ) :
    degreeFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU (k - 1) ⟶
      degreeFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU k := by
  cases k with
  | zero => exact 0
  | succ k => exact differentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k

/-- This zero-aware presentation has exactly the original incoming boundary. -/
theorem incomingDifferentialNat_range
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    LinearMap.range
      (SmoothRep.hom ((incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k).app A)).toLinearMap =
        boundary.{uI, uG, uV} P M U h hclosed hδ hP hU A k := by
  cases k with
  | zero => exact LinearMap.range_zero
  | succ k => rfl

/-- Exactness at the actual quotient, with no injectivity premise on the differential. -/
theorem incomingDifferentialNat_exact
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    LinearMap.range
      (SmoothRep.hom ((incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k).app A)).toLinearMap =
        LinearMap.ker (SmoothRep.hom
          ((terminalProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU k).app A)).toLinearMap := by
  rw [incomingDifferentialNat_range]
  exact (terminalProjection_ker.{uI, uG, uV} P M U h hclosed hδ hP hU A k).symm

variable {H : Type uH} [Group H] [TopologicalSpace H]
variable (J : SmoothRep.{0, uG, max uI uG uV} ℂ G ⥤
  SmoothRep.{0, uH, max uI uG uV} ℂ H)
variable (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

/-- The actual cokernel of the mapped incoming signed differential is naturally
the exact functor applied to the original retained terminal quotient. -/
def terminalCokernelIso (k : ℕ) :
    SmoothNatCokernel.functor (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k) J) ≅
        terminalFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU k ⋙ J :=
  ExactSmoothTransport.cokernelIso J hJ
    (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k)
    (terminalProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU k)
    (fun A => incomingDifferentialNat_exact.{uI, uG, uV} P M U h hclosed hδ hP hU A k)
    (fun A => terminalProjection_surjective.{uI, uG, uV} P M U h hclosed hδ hP hU A k)

/-- On representatives, the comparison is the mapped actual terminal projection. -/
@[simp]
theorem terminalCokernelIso_projection (k : ℕ)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (v : J.obj ((degreeFunctor.{uI, uG, uV} P M U h hclosed hδ hP hU k).obj A)) :
    SmoothRep.hom ((terminalCokernelIso P M U h hclosed hδ hP hU J hJ k).hom.app A)
      (SmoothRep.hom ((SmoothNatCokernel.projection (Functor.whiskerRight
        (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k) J)).app A) v) =
      SmoothRep.hom (J.map
        ((terminalProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU k).app A)) v :=
  ExactSmoothTransport.cokernelIso_projection J hJ
    (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k)
    (terminalProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU k)
    (fun A => incomingDifferentialNat_exact.{uI, uG, uV} P M U h hclosed hδ hP hU A k)
    (fun A => terminalProjection_surjective.{uI, uG, uV} P M U h hclosed hδ hP hU A k) A v

/-- The projection compatibility is an equality of natural transformations. -/
theorem terminalCokernelIso_projection_nat (k : ℕ) :
    SmoothNatCokernel.projection (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U h hclosed hδ hP hU k) J) ≫
        (terminalCokernelIso P M U h hclosed hδ hP hU J hJ k).hom =
      Functor.whiskerRight (terminalProjectionNat.{uI, uG, uV} P M U h hclosed hδ hP hU k) J := by
  ext A v
  exact terminalCokernelIso_projection P M U h hclosed hδ hP hU J hJ k A v

end Langlands.Aubert.General.Complex
