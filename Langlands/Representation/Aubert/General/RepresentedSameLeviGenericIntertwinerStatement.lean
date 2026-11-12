import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity

/-! # Generic nonzero morphisms between represented inductions sharing a Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For two actual represented parabolics `P = MN` and `Q = MU` of a connected reductive
group with the same Levi scheme `M`, and an irreducible admissible representation `σ`
of `M(F)`, there is a nonzero polynomial in the published finite coordinates of the
unramified characters of `M(F)` off whose zero locus some morphism
`i_P^G(σψ) → i_Q^G(σψ)` is nonzero. -/
def RepresentedSameLeviGenericNonzeroIntertwinerStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      letI := leviPointTopology l hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), σ.IsIrreducible → σ.IsAdmissible →
        ∃ poly : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, poly ≠ 0 ∧
          ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive poly,
            ∃ f : (leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj
                  (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) ⟶
                (leviInductionFunctor.{u, v} q lQ rQ hq hrQ hlQ hmulQ).obj
                  (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)),
              f ≠ 0

end Langlands.Aubert.General.RepresentedParabolic
