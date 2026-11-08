import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! # The centre of `R_Ω` lies in the centre of `R_D` (Renard VI.10.4, second Lemma)

With `Π_D = ind_{⁰M}^M(ρ₀)`, `R_D = End_M(Π_D)` embedded in `R_Ω = End_G(i_P^G(Π_D))` by
parabolic induction, the centre `ℨ_Ω` of `R_Ω` is contained in the centre `ℨ_D` of `R_D`; hence
`ℨ_Ω` is the set of elements of `ℨ_D` commuting with all of `R_Ω`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.4, the Lemma `ℨ_Ω ⊂ ℨ_D` and its consequence `ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)`, for an
actual rational parabolic `P = MN`, an irreducible supercuspidal representation `π` of
`M(F)`, an irreducible `ρ₀` of `⁰M(F)` embedded in `π|_{⁰M(F)}` and
`Π_D = ind_{⁰M(F)}^{M(F)} ρ₀`: the centre of `End(i_P^G Π_D)` is exactly the set of
`i_P^G(z)`, `z` in the centre of `End(Π_D)`, that commute with every element of
`End(i_P^G Π_D)`. -/
def InducedProgeneratorCenterInclusionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      haveI := hl.isConnectedReductive.smooth
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible → IsSupercuspidal π →
      ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M),
        ρ₀.IsIrreducible →
        ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
          Function.Injective (SmoothRep.hom j) →
          let piD := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀
          let I := leviInductionFunctor p l r hp hr hl hmul
          (Subring.center (End (I.obj piD)) : Set (End (I.obj piD))) =
            {x : End (I.obj piD) | ∃ z ∈ Subring.center (End piD),
              x = I.map z ∧ ∀ a : End (I.obj piD), a * x = x * a}

end Langlands.Aubert.General.RepresentedParabolic
