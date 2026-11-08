import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Independence of the induced progenerator (Renard VI.10.1)

Let `(M, ρ)` be a cuspidal datum, `D = [M, ρ]_M` and `Π_D = ind_{⁰M}^M(ρ₀)` the progenerator of
`M(M)_D` of VI.4.1, built from an irreducible summand `ρ₀` of `ρ|_{⁰M}`. Renard's Lemma,
Proposition and Corollary of VI.10.1 show that `i_P^G(Π_D)` does not depend, up to a
non-canonical isomorphism, on the parabolic `P` with Levi factor `M`, nor on replacing
`(M, D)` by a conjugate `(w · M, w · D)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.1, Lemma, Proposition and Corollary, combined in derived form: let
`P = MN` and `P' = M'N'` be actual rational parabolics of `G`, and let `g ∈ G(F)` conjugate
`M` onto `M'` through an isomorphism `φ : M ≅ M'` with `g ι(m) g⁻¹ = ι'(φ m)` (`ι = l ≫ p`,
`ι' = l' ≫ p'`). Let `π` be an irreducible supercuspidal representation of `M(F)` and `ρ₀` an
irreducible representation of the common norm kernel `⁰M(F)` embedded in `π|_{⁰M(F)}`, and
`Π_D = ind_{⁰M(F)}^{M(F)} ρ₀`. Then `i_P^G(Π_D) ≅ i_{P'}^G(Π_D ∘ φ⁻¹)`; the right side is
`i_{P'}^G(Π_{w · D})` for the conjugate datum. -/
def InducedProgeneratorIndependenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (p' : P' ⟶ G) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r'))
      (g : rationalPoints G) (φ : M ≅ M'),
      φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom →
      haveI := hl.isConnectedReductive.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      haveI := hl.isConnectedReductive.smooth
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hl'.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M') := leviPointTopology l' hl'
      ∀ e : rationalPoints M' ≃ₜ* rationalPoints M,
        (∀ m', e m' = rationalPoints.map φ.inv m') →
        ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible → IsSupercuspidal π →
        ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M),
          ρ₀.IsIrreducible →
          ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
            Function.Injective (SmoothRep.hom j) →
            Nonempty ((leviInductionFunctor p l r hp hr hl hmul).obj
                (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ≅
              (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj
                (SmoothRep.pullback e (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)))

end Langlands.Aubert.General.RepresentedParabolic
