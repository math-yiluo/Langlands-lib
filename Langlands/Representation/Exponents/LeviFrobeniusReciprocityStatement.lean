import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Frobenius reciprocity for normalized parabolic induction

Renard 2026, VI.1.2 Proposition (printed p.136/PDF p.142), adjunction part: for a
parabolic `P = MN` of `G`, normalized parabolic induction `i_P^G : M(M) → M(G)` is
right adjoint to normalized parabolic restriction `r_P^G : M(G) → M(M)`. Both functors
are the published normalized functors of a represented parabolic, transported to smooth
representations of `M(F)` through the Levi-point identification. The adjunction is
stated as the explicit evaluation-at-identity bijection of intertwiner spaces, with
independent carrier universes.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.2 Proposition, adjunction part (Frobenius reciprocity): for every
actual rational parabolic with rational Levi and matching geometric unipotent radical,
every smooth representation `π` of `G(F)` and every smooth representation `σ` of
`M(F)`, evaluation at the identity of `G(F)` descends through the normalized Jacquet
quotient and gives a linear bijection
`Hom_G(π, i_P^G σ) ≃ Hom_M(r_P^G π, σ)`. -/
def LeviFrobeniusReciprocityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
        (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        ∃ e : π.representation.IntertwiningMap
              ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation ≃ₗ[ℂ]
            ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
              σ.representation,
          ∀ (F : π.representation.IntertwiningMap
              ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation) (x : π),
            e F (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x) =
              Induction.eval (pointImage p)
                (inducingRepresentation
                  (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                  (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                  (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
                (F x) 1

end Langlands.Aubert.General.RepresentedParabolic
