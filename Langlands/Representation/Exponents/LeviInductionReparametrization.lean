import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Normalized induction does not depend on the parametrization of the Levi -/

noncomputable section

universe u v uG uK uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]

/-- Normalized induction from two literally equal Levi subgroups `L = L'` of the same
parabolic, of representations pulled back from one representation `σ` of a group `K`
through equivalences that agree on `L = L'`, gives the same representation. -/
theorem normalizedInductionFunctor_obj_pullback_congr {K : Type uK} [Group K]
    [TopologicalSpace K] {P L L' N : Subgroup Γ} (hL : L = L')
    (h : IsSemidirectDecomposition P L N) (h' : IsSemidirectDecomposition P L' N)
    (hN : IsClosed (N : Set Γ)) (φ : L ≃ₜ* K) (φ' : L' ≃ₜ* K)
    (hφ : ∀ x : L, φ' ⟨x, hL ▸ x.2⟩ = φ x) (σ : SmoothRep.{0, uK, uV} ℂ K) :
    (normalizedInductionFunctor h hN).obj (SmoothRep.pullback φ σ) =
      (normalizedInductionFunctor h' hN).obj (SmoothRep.pullback φ' σ) := by
  subst hL
  obtain rfl : φ' = φ := ContinuousMulEquiv.ext fun x => hφ x
  rfl

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G Q L M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviReparametrizationAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction along two Levi maps `lQ : L → Q` and `lQ' : M → Q` of the same
parabolic, related by a point equivalence `φ : M(k) ≃ L(k)` over `G(k)`, agrees with the
pullback along `φ`: `i_{Q, lQ'}(φ^* τ) = i_{Q, lQ}(τ)`. -/
theorem leviInductionFunctor_obj_pullback_eq
    (q : Q ⟶ G) (lQ : L ⟶ Q) (lQ' : M ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : IsRationalLeviSubgroup lQ) (hlQ' : IsRationalLeviSubgroup lQ')
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hmulQ' : IsIso (subgroupMultiplication lQ' rQ))
    (φ : letI := leviPointTopology lQ' hlQ'; letI := leviPointTopology lQ hlQ
      rationalPoints M ≃ₜ* rationalPoints L)
    (hφ : ∀ m, rationalPoints.map (lQ ≫ q) (φ m) = rationalPoints.map (lQ' ≫ q) m)
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, v} ℂ (rationalPoints L)) :
    letI := leviPointTopology lQ' hlQ'
    letI := leviPointTopology lQ hlQ
    (leviInductionFunctor q lQ' rQ hq hrQ hlQ' hmulQ').obj (SmoothRep.pullback φ τ) =
      (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj τ := by
  let := leviPointTopology lQ' hlQ'
  let := leviPointTopology lQ hlQ
  have hL : pointImage (lQ' ≫ q) = pointImage (lQ ≫ q) := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨φ m, hφ m⟩
    · rintro ⟨m, rfl⟩
      refine ⟨φ.symm m, ?_⟩
      change rationalPoints.map (lQ' ≫ q) (φ.symm m) = rationalPoints.map (lQ ≫ q) m
      rw [← hφ, ContinuousMulEquiv.apply_symm_apply]
  exact normalizedInductionFunctor_obj_pullback_congr hL _ _ _
    ((leviPointsEquiv q lQ' hq hlQ').symm.trans φ) (leviPointsEquiv q lQ hq hlQ).symm
    (fun x => by
      apply (leviPointsEquiv q lQ hq hlQ).injective
      apply Subtype.ext
      rw [ContinuousMulEquiv.apply_symm_apply]
      change (x : rationalPoints G) =
        rationalPoints.map (lQ ≫ q) (φ ((leviPointsEquiv q lQ' hq hlQ').symm x))
      rw [hφ, ← leviPointsEquiv_apply_coe q lQ' hq hlQ', ContinuousMulEquiv.apply_symm_apply])
    τ

end Langlands.Aubert.General.RepresentedParabolic
