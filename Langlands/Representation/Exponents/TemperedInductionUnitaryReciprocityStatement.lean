import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.GroupScheme.Reductive.Basic

/-! # Tempered Frobenius reciprocity through the unitary Jacquet part

Renard 2026, VII.2.4, Proposition (printed p.229/PDF p.235): for a parabolic `P = MN` of
`G`, every tempered representation `σ` of `M` and every tempered representation `π` of
`G`, there is a natural isomorphism `Hom_G(π, i_P^G σ) ≃ Hom_M((r_P^G π)_0, σ)`. The
isomorphism is stated explicitly: an intertwiner `F` is sent to the map taking the class
of a vector `x` in the unitary part to the value of `F x` at the identity. Carrier
universes of `π` and `σ` are independent.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.4, Proposition: for every actual rational parabolic with rational Levi,
matching geometric unipotent radical and split component, every normalized-exponent
tempered `π` of `G(F)` and every normalized-exponent tempered `σ` of `M(F)`, there is a
linear bijection `Hom_G(π, i_P^G σ) ≃ Hom_M((r_P^G π)_0, σ)` sending `F` to the map
whose value at an element of the unitary part with Jacquet class `[x]` is `(F x)(1)`. -/
def TemperedInductionUnitaryReciprocityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
        (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        IsNormalizedExponentTempered hG π →
          IsNormalizedExponentTempered hl.isConnectedReductive σ →
            ∃ e : π.representation.IntertwiningMap
                  ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation ≃ₗ[ℂ]
                (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
                  σ.representation,
              ∀ (F : π.representation.IntertwiningMap
                  ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
                (y : leviUnitaryJacquetModule p l r hp hl hr hmul ha π) (x : π),
                SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π) y =
                    Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x →
                  e F y =
                    Induction.eval (pointImage p)
                      (inducingRepresentation
                        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
                      (F x) 1

end Langlands.Aubert.General.RepresentedParabolic
