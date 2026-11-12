import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityReduction
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement

/-! # The unique Langlands quotient from four closed prerequisites

The exact part-(i) statement follows from second adjointness, preservation
of finite length, opposite identity support and opposite kernel regularity.
Actual opposite existence and all carrier comparisons are constructed.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The exact universal uniqueness component follows from four existing
closed propositions. Their proofs are still required for the unconditional result. -/
theorem langlandsQuotientUnique_of_inputs
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (hfinite : LeviInductionFiniteLengthStatement.{u, v})
    (hS : OppositeIdentitySupportStatement.{u, v})
    (hK : LanglandsTripletOppositeKernelStatement.{u, v}) :
    LanglandsQuotientUniqueStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  let O := oppositeLeviParabolic hG p l hp hl
  obtain ⟨adj⟩ := hAdj k G hG P O.parabolic M U O.radical p l r hp hl hr hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    O.levi_comp O.intersection
  have hfin := hfinite k G hG P M U p l r hp hl hr hmul
  have hreg := hK k G hG T i ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    O.parabolic O.radical O.inclusion O.levi O.unipotent
    O.isParabolic O.isLevi O.isRadical O.multiplication O.levi_comp O.intersection hTrip
  obtain ⟨eS⟩ := hS k G hG P M U O.parabolic O.radical p l r hp hl hr hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    O.levi_comp O.intersection τ
  exact exists_regularOppositeLeviHead p l r hp hl hr hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    hG a ha adj hfin τ hirr hadm hreg eS

/-- Choose a Langlands quotient and its full strong-head certificate from
the four closed prerequisites, with the original triplet telescope. -/
def langlandsTripletHeadOfInputs
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (hfinite : LeviInductionFiniteLengthStatement.{u, v})
    (hS : OppositeIdentitySupportStatement.{u, v})
    (hK : LanglandsTripletOppositeKernelStatement.{u, v})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl),
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        {π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G) //
          Classification.IsIrreducibleHead
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              (σ.twist ψ.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation
            π.representation} := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ hTrip
  let H := langlandsQuotientUnique_of_inputs hAdj hfinite hS hK
    k G hG T i ν D P M U A p l r a hp hl hr hmul ha J f σ ψ hTrip
  exact ⟨H.choose, H.choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic
