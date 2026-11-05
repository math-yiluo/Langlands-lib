import Langlands.Representation.Exponents.SplitComponentFiniteSupport
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.BruhatTits.Parabolic.QuotientCompactStatement

/-! # Dynamic compactness and finite exponents for represented parabolics -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance finiteReductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- The existing dynamic compactness target supplies compactness for the literal
point image of a represented parabolic, once parabolics are known to be dynamic. -/
theorem compactSpace_leftQuotient_pointImage_of_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G) (p : P ⟶ G) (hp : IsParabolicSubgroup p) :
    CompactSpace (Induction.LeftQuotient (pointImage p)) := by
  obtain ⟨χ, hχ⟩ := (hPD k G hG P p hp.isClosedSubgroup).1 hp
  have hpoints : pointImage p =
      (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    congrArg (fun H : SubgroupFunctor G =>
      H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hχ
  rw [hpoints]
  exact (hcompact k G hG χ).2

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Only the two existing structural statements and actual Jacquet spanning
remain in this finite-exponent reduction; Jacquet finite length is unnecessary. -/
theorem finite_normalizedJacquetExponents_of_dynamic_of_spanning
    (hPD : ParabolicDynamicStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hfinite : π.HasFiniteLength)
    (hspan : (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤) :
    (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite := by
  let := compactSpace_leftQuotient_pointImage_of_dynamic hPD hcompact hG p hp
  exact finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning
    p l r hp hl hr hmul ha π hfinite hspan

/-- A uniform conditional reduction of the finite-exponent part of VII.1.1,
retaining all actual parabolic and split-component data. -/
def ArbitraryParabolicFiniteSupportReductionStatement : Prop :=
  ParabolicDynamicStatement.{u} →
    BruhatTits.DynamicParabolicQuotientCompactStatement.{u} →
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
          (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
          (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
          π.HasFiniteLength →
            (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
              (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤ →
                (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite

theorem arbitraryParabolicFiniteSupport_reduction :
    ArbitraryParabolicFiniteSupportReductionStatement.{u, v} := by
  intro hPD hcompact k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U A p l r a hp hl hr hmul ha π hfinite hspan
  exact finite_normalizedJacquetExponents_of_dynamic_of_spanning hPD hcompact hG
    p l r hp hl hr hmul ha π hfinite hspan

end Langlands.Aubert.General.RepresentedParabolic
