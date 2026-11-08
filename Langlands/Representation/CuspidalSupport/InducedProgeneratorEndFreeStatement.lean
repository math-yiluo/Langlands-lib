import Mathlib.GroupTheory.DoubleCoset
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Category.Twist
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # The endomorphism ring of the induced progenerator (Renard VI.10.4, Lemma)

Let `Π_D = ind_{⁰M}^M(ρ₀)` be the progenerator of VI.4.1 for an irreducible supercuspidal
representation `π` of `M(F)`, `R_D = End_M(Π_D)` and `R_Ω = End_G(i_P^G(Π_D))`. Parabolic
induction embeds `R_D` in `R_Ω`, and `R_Ω` is a free right `R_D`-module of rank `|W(D)|`, hence
free of finite rank over the centre of `R_D`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.4, the embedding `i_P^G : R_D → R_Ω` and the Lemma, in derived form: let
`P = MN` be an actual rational parabolic of `G`, `π` an irreducible supercuspidal
representation of `M(F)`, `ρ₀` an irreducible representation of `⁰M(F)` embedded in
`π|_{⁰M(F)}`, and `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀`. Let `W` be the set of double cosets
`P(F) w P(F)` of elements `w` normalizing `M` (through `φ : M ≅ M`) such that `π ∘ φ` is an
unramified twist of `π`, the actual-group form of `W(D)`. Then

* `a ↦ i_P^G(a)` is injective on `End(Π_D)`;
* `W` is finite and there are `b₁, …, b_n ∈ End(i_P^G Π_D)`, `n = |W|`, such that every
  `x ∈ End(i_P^G Π_D)` is uniquely `x = ∑ bᵢ ∘ i_P^G(aᵢ)` with `aᵢ ∈ End(Π_D)`;
* there are finitely many `c₁, …, c_m` such that every `x` is uniquely `∑ cⱼ ∘ i_P^G(zⱼ)` with
  `zⱼ` in the centre of `End(Π_D)`. -/
def InducedProgeneratorEndFreeStatement : Prop :=
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
          let W : Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
              (pointImage p : Set (rationalPoints G))) :=
            {x | ∃ (w : rationalPoints G) (φ : M ≅ M)
                (e : rationalPoints M ≃ₜ* rationalPoints M)
                (χ : Plancherel.unramifiedCharacters
                  (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
              DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
                φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom ∧
                (∀ m, e m = rationalPoints.map φ.hom m) ∧
                Nonempty (SmoothRep.pullback e π ≅
                  π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ))}
          let piD := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀
          let I := leviInductionFunctor p l r hp hr hl hmul
          Function.Injective (fun a : piD ⟶ piD => I.map a) ∧
            W.Finite ∧
            (∃ b : Fin W.ncard → (I.obj piD ⟶ I.obj piD),
              ∀ x : I.obj piD ⟶ I.obj piD,
                ∃! a : Fin W.ncard → (piD ⟶ piD), x = ∑ i, I.map (a i) ≫ b i) ∧
            ∃ (m : ℕ) (c : Fin m → (I.obj piD ⟶ I.obj piD)),
              ∀ x : I.obj piD ⟶ I.obj piD,
                ∃! z : Fin m → Subring.center (End piD),
                  x = ∑ i, I.map ((z i : End piD) : piD ⟶ piD) ≫ c i

end Langlands.Aubert.General.RepresentedParabolic
