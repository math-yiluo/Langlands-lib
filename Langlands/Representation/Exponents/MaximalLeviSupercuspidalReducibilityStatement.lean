import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Reducibility of representations induced from supercuspidals of maximal Levis

Renard 2026, VII.1.3, Theorem (printed pp.224–226/PDF pp.230–232): let `P = MN` be a
maximal parabolic and `ρ` an irreducible supercuspidal representation of `M`. If
`i_P^G ρ` is reducible, then the nontrivial element `w` of `W(M, *)` normalizes `M`
and `ρ^w ≃ ρ ψ` for an unramified character `ψ` of `M` with values in `ℝ_{>0}`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.3, Theorem: for every actual maximal proper rational parabolic with
rational Levi `M` and matching radical, and every irreducible supercuspidal smooth
representation `ρ` of `M(F)` (every normalized Jacquet module of `ρ` for a proper
parabolic of `M` vanishes) whose normalized induction is reducible, some `g ∈ G(F)`
outside the Levi image normalizes the Levi through an automorphism `φ` of `M`, and
`ρ ∘ φ(F)⁻¹` is isomorphic to `ρ` twisted by an unramified character of `M(F)` with
positive real values. -/
def MaximalLeviSupercuspidalReducibilityStatement : Prop :=
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
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
        IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        ¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible →
        ∃ (g : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            (∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
              (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t) ∧
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) =
                (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                  ρ.representation (rationalPoints.map φ.hom m) (T x)

end Langlands.Aubert.General.RepresentedParabolic
