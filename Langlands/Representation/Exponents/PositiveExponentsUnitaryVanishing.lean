import Langlands.GroupScheme.Rational.ProperParabolicRestrictedRoot
import Langlands.Representation.Exponents.UnitaryJacquetExponents

/-! # Vanishing of the unitary part from strict normalized exponents -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance positiveVanishingAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

include hG pres in
/-- Strict positivity for one compatible presentation excludes all unitary
exponents and makes the original proper-parabolic unitary Jacquet part zero. -/
theorem unitaryJacquetPart_eq_bot_of_positive_exponents
    (hproper : ¬ IsIso p)
    (hpos : ∀ χ : rationalPoints A.toGrp →* ℂˣ,
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
          pres.positiveCone) :
    unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  apply (unitaryJacquetPart_eq_bot_iff p l r hp hl hr hmul ha π).mpr
  intro χ hχ hzero
  have hmem := hpos χ hχ
  rw [hzero] at hmem
  exact pres.zero_notMem_positiveCone_of_not_isIso hG hproper hmem

end Langlands.Aubert.General.RepresentedParabolic
