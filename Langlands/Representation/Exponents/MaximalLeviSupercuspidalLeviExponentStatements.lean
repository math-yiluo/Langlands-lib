import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly

/-! # Exponents along the parabolics with Levi factor `M` in Renard VII.1.3

The exponent part of the proof of Renard VII.1.3 (PDF pp.230–232) splits into two steps.
For a sub or quotient `W` of `i_P^G ρ`, with `P = MN` maximal and `ρ` supercuspidal, the
exponents of `W` along an arbitrary parabolic are controlled by its exponents along the
parabolics with Levi factor exactly `M` (transfer). One irreducible sub or quotient has
positive exponents along those parabolics (Renard's choice of `π₁`). This module states the
two steps; nothing is proved here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section LeviCone

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance leviConeAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The positive-cone condition of `HasPositiveRepresentedJacquetExponents`, restricted to
the actual rational parabolics `q : Q ⟶ G` whose rational Levi `lQ : M ⟶ Q` has the same
source `M` and the same composite `lQ ≫ q = m` into `G`. -/
def HasPositiveLeviJacquetExponents (m : M ⟶ G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  ∀ (Q U : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q) (a : A.toGrp ⟶ M)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ)) (ha : IsSplitComponent a)
    (pres : ParabolicRootPresentation q lQ a) (χ : rationalPoints A.toGrp →* ℂˣ),
    lQ ≫ q = m →
    IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π χ →
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.positiveCone

end LeviCone

/-- Transfer step of the exponent argument for Renard VII.1.3: for an actual maximal proper
rational parabolic `P = MN` and an irreducible supercuspidal `ρ` of `M(F)` such that
`i_P^G ρ` has a unitary central character, every subrepresentation or quotient of
`i_P^G ρ` whose exponents along the parabolics with Levi factor `M` lie in the positive
cones satisfies the full represented positive-cone condition of Casselman's criterion. -/
def MaximalLeviSupercuspidalExponentTransferStatement : Prop :=
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
        Nonempty (UnitaryCentralCharacter
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation) →
        ∀ W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          ((∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ,
              Function.Injective (SmoothRep.hom f)) ∨
            ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W,
              Function.Surjective (SmoothRep.hom f)) →
          HasPositiveLeviJacquetExponents (l ≫ p) W →
          HasPositiveRepresentedJacquetExponents W

/-- Constituent step of the exponent argument for Renard VII.1.3: for an actual maximal
proper rational parabolic `P = MN` and an irreducible supercuspidal `ρ` of `M(F)` whose
central character is not unitary, if `i_P^G ρ` is reducible with a unitary central
character, then it has an irreducible subrepresentation or quotient whose exponents along
every parabolic with Levi factor `M` lie in the positive cones. -/
def MaximalLeviSupercuspidalLeviPositiveConstituentStatement : Prop :=
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
          W.IsIrreducible ∧ HasPositiveLeviJacquetExponents (l ≫ p) W ∧
          ((∃ f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ,
              Function.Injective (SmoothRep.hom f)) ∨
            ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W,
              Function.Surjective (SmoothRep.hom f))

end Langlands.Aubert.General.RepresentedParabolic
