import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly

/-! # A positive-exponent constituent of a reducible maximal-Levi induction

The exponent part of the proof of Renard VII.1.3 (PDF pp.230–232): a reducible
`i_P^G ρ`, for `P` maximal and `ρ` irreducible supercuspidal with non-unitary central
character, has an irreducible subrepresentation or quotient whose Jacquet exponents
satisfy the condition of Casselman's criterion (VII.1.2).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The exponent part of the proof of Renard VII.1.3: for an actual maximal proper rational
parabolic and an irreducible supercuspidal `ρ` of `M(F)` whose central character is not
unitary, if `i_P^G ρ` is reducible with a unitary central character, then it has an
irreducible subrepresentation or quotient all of whose normalized Jacquet exponents, along
every actual rational parabolic and compatible root presentation, have normalized real part
in the strictly positive root cone. -/
def MaximalLeviSupercuspidalPositiveConstituentStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
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
        IsEmpty (UnitaryCentralCharacter ρ.representation) →
        ¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible →
        Nonempty (UnitaryCentralCharacter
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation) →
        ∃ W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          W.IsIrreducible ∧ HasPositiveRepresentedJacquetExponents W ∧
          ((∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ,
              Function.Injective (SmoothRep.hom f)) ∨
            ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W,
              Function.Surjective (SmoothRep.hom f))

end Langlands.Aubert.General.RepresentedParabolic
