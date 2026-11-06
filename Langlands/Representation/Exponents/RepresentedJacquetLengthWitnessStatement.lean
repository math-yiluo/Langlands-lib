import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement
import Langlands.Representation.Filtration.ExactFamilyLengthStatement
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

/-! # Actual Jacquet families witnessing a composition-length bound -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Witness

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance witnessAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- A finite family of actual normalized Jacquet functors, with compact-limit radicals,
whose total image length is bounded and which detects every irreducible subquotient.
No finite-length assumption on the source is part of this internal predicate. -/
def HasRepresentedJacquetLengthWitness
    (A : SmoothRep.{0, u, w} ℂ (rationalPoints G)) (bound : ℕ) : Prop :=
  ∃ (n : ℕ) (P M U : Fin n → GroupScheme (Spec (CommRingCat.of k)))
    (p : ∀ i, P i ⟶ G) (l : ∀ i, M i ⟶ P i) (r : ∀ i, U i ⟶ P i)
    (hp : ∀ i, IsParabolicSubgroup (p i))
    (hl : ∀ i, IsRationalLeviSubgroup (l i))
    (hr : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (r i))
    (hmul : ∀ i, IsIso (subgroupMultiplication (l i) (r i))),
    (∀ i, Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r i ≫ p i))) ∧
    ∃ b : Fin n → ℕ, (∑ i, b i) ≤ bound ∧
      (∀ i, letI := leviPointTopology (l i) (hl i)
        repLength ((leviJacquetFunctor (p i) (l i) (r i)
          (hp i) (hr i) (hl i) (hmul i)).obj A).representation ≤ (b i : ℕ∞)) ∧
      (∀ D : SmoothRep.{0, u, w} ℂ (rationalPoints G),
        D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ i, letI := leviPointTopology (l i) (hl i)
          Nontrivial ((leviJacquetFunctor (p i) (l i) (r i)
            (hp i) (hr i) (hl i) (hmul i)).obj D))

end Witness

/-- The geometric/support input to the length bound in Renard VI.5.4, specialized
to the maximal proper Levi used in VII.1.3. This declaration is an unproved target. -/
def MaximalLeviSupercuspidalJacquetLengthWitnessStatement : Prop :=
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
        HasRepresentedJacquetLengthWitness
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) 2

end Langlands.Aubert.General.RepresentedParabolic
