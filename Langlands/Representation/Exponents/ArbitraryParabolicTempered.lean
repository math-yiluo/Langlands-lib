import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Plancherel.SplitTorusRealPart
import Langlands.GroupScheme.Rational.ParabolicRootPresentation

/-! # Normalized-exponent temperedness for all actual rational parabolics

This derived formulation of Renard VII.2.1 uses the explicitly normalized
q^(-s) parameter. The distinct raw logarithmic convention in V.3.20 and the
remaining source-comparison obligation are documented in the paired Markdown.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

section ConeCondition

variable [LocallyOfFiniteType G.X.hom]
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (ha : IsSplitComponent a)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The normalized exponent condition for specified actual maps. Nonempty
presentation coverage is required before testing every compatible presentation
and every matching represented radical decomposition. -/
def SatisfiesNormalizedExponentConeCondition : Prop :=
  Nonempty (ParabolicRootPresentation p l a) ∧
    ∀ (pres : ParabolicRootPresentation p l a)
      (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (χ : rationalPoints A.toGrp →* ℂˣ),
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
          pres.nonnegCone

/-- Missing compatible presentations cannot make the condition true. -/
theorem SatisfiesNormalizedExponentConeCondition.nonempty_presentation
    (h : SatisfiesNormalizedExponentConeCondition p l a hp hl ha π) :
    Nonempty (ParabolicRootPresentation p l a) :=
  h.1

/-- Every compatible presentation gives the required cone membership for any
actual matching radical and normalized Jacquet exponent. -/
theorem SatisfiesNormalizedExponentConeCondition.normalizedRealPart_mem_nonnegCone
    (h : SatisfiesNormalizedExponentConeCondition p l a hp hl ha π)
    (pres : ParabolicRootPresentation p l a)
    {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.nonnegCone :=
  h.2 pres U r hr hmul χ hχ

/-- For a supplied exponent, the condition yields an actual presentation with
cone membership as well as membership in every supplied presentation. -/
theorem SatisfiesNormalizedExponentConeCondition.exists_presentation_mem_nonnegCone
    (h : SatisfiesNormalizedExponentConeCondition p l a hp hl ha π)
    {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    ∃ pres : ParabolicRootPresentation p l a,
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
        pres.nonnegCone := by
  obtain ⟨pres⟩ := h.1
  exact ⟨pres, h.2 pres U r hr hmul χ hχ⟩

end ConeCondition

/-- Admissibility and the normalized exponent condition for every actual
rational parabolic, rational Levi and split component. The reductive hypothesis
supplies local finite type for the actual root cones. -/
def IsNormalizedExponentTempered (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  haveI := hG.smooth
  IsAdmissible π.representation ∧
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (ha : IsSplitComponent a),
      SatisfiesNormalizedExponentConeCondition p l a hp hl ha π

variable {hG : IsConnectedReductive G}
  {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Admissibility is part of normalized-exponent temperedness. -/
theorem IsNormalizedExponentTempered.isAdmissible
    (h : IsNormalizedExponentTempered hG π) : IsAdmissible π.representation :=
  h.1

/-- Extract the condition for any specified actual parabolic, Levi and split
component, with the finite-type instance supplied by connected reductivity. -/
theorem IsNormalizedExponentTempered.parabolic
    (h : IsNormalizedExponentTempered hG π)
    {P M : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (ha : IsSplitComponent a) :
    haveI := hG.smooth
    SatisfiesNormalizedExponentConeCondition p l a hp hl ha π :=
  h.2 P M A p l a hp hl ha

/-- In particular, each specified triple admits an actual compatible
presentation whenever the representation satisfies the definition. -/
theorem IsNormalizedExponentTempered.nonempty_presentation
    (h : IsNormalizedExponentTempered hG π)
    {P M : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (ha : IsSplitComponent a) :
    Nonempty (ParabolicRootPresentation p l a) :=
  (h.2 P M A p l a hp hl ha).1

end Langlands.Aubert.General.RepresentedParabolic
