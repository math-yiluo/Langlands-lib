import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityProof
import Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement
import Mathlib.RepresentationTheory.Semisimple

/-! # Unitary Jacquet nonvanishing for a quotient of semisimple induction -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)

include hG

section

variable [IsAffineHom G.X.hom]

local instance inductionQuotientAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)
  (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

set_option maxHeartbeats 800000 in
/-- Split a nonzero quotient map from the actual semisimple induction and apply
tempered reciprocity to obtain an actual nonzero map from the unitary Jacquet part. -/
def unitaryJacquetMapOfSemisimpleInductionQuotient
    (hπ : π.IsIrreducible)
    (hsemisimple : letI := leviPointTopology l hl
      Representation.IsSemisimpleRepresentation
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hπtemp : IsNormalizedExponentTempered hG π)
    (hσtemp : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (F : letI := leviPointTopology l hl
      Representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation)
    (hF : F ≠ 0) :
    letI := leviPointTopology l hl
    {f : Representation.IntertwiningMap
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation σ.representation //
      f ≠ 0} := by
  let := leviPointTopology l hl
  have := hl.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let I := (leviInductionFunctor p l r hp hr hl hmul).obj σ
  letI : π.representation.IsIrreducible := hπ
  have hsurj : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  letI : IsSemisimpleModule (MonoidAlgebra ℂ (rationalPoints G)) I.representation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hsemisimple
  let f := Representation.IntertwiningMap.equivLinearMapAsModule
    I.representation π.representation F
  have hf : Function.Surjective f := hsurj
  apply Classical.choice
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f hf
    (LinearMap.id : π.representation.asModule →ₗ[MonoidAlgebra ℂ (rationalPoints G)]
      π.representation.asModule)
  let S : π.representation.IntertwiningMap I.representation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      π.representation I.representation).symm s
  have hS : S ≠ 0 := by
    intro hz
    apply hF
    ext x
    have hx := congrArg
      (fun t : π.representation.asModule →ₗ[MonoidAlgebra ℂ (rationalPoints G)]
        π.representation.asModule => t (F x)) hs
    change F (S (F x)) = F x at hx
    rw [hz] at hx
    change F 0 = F x at hx
    change F x = 0
    simpa only [map_zero] using hx.symm
  obtain ⟨e, _⟩ := temperedInductionUnitaryReciprocity k G hG
    P M U A p l r a hp hl hr hmul ha π σ hπtemp hσtemp
  refine ⟨⟨e S, ?_⟩⟩
  intro hz
  apply hS
  apply e.injective
  simpa only [map_zero] using hz

set_option maxHeartbeats 800000 in
/-- The target unitary Jacquet summand of an irreducible tempered quotient of
semisimple induction is nonzero, for a tempered inducing representation. -/
theorem unitaryJacquetPart_ne_bot_of_semisimple_induction_quotient
    (hπ : π.IsIrreducible)
    (hsemisimple : letI := leviPointTopology l hl
      Representation.IsSemisimpleRepresentation
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hπtemp : IsNormalizedExponentTempered hG π)
    (hσtemp : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (F : letI := leviPointTopology l hl
      Representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation)
    (hF : F ≠ 0) :
    unitaryJacquetPart p l r hp hl hr hmul ha π ≠ ⊥ := by
  let := leviPointTopology l hl
  let f := unitaryJacquetMapOfSemisimpleInductionQuotient
    hG p l r hp hl hr hmul ha π σ hπ hsemisimple hπtemp hσtemp F hF
  intro hbot
  apply f.property
  ext x
  have hx : x = 0 := by
    apply Subtype.ext
    exact hbot.le x.property
  change f.val x = 0
  rw [hx, map_zero]

include ha

set_option maxHeartbeats 800000 in
/-- Conditional assembly of the second fullness step in VII.2.6: the exact
VII.2.4 criterion rules out a proper parabolic for a square-integrable target. -/
theorem isIso_of_squareIntegrable_semisimple_induction_quotient
    (hcriterion : TemperedSquareIntegrableUnitaryPartStatement.{u, w})
    [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
    [haar.IsHaarMeasure]
    (hπsquare : IsSquareIntegrableModCenter π.representation haar)
    (hπ : π.IsIrreducible)
    (hsemisimple : letI := leviPointTopology l hl
      Representation.IsSemisimpleRepresentation
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hπtemp : IsNormalizedExponentTempered hG π)
    (hσtemp : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (F : letI := leviPointTopology l hl
      Representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation)
    (hF : F ≠ 0) : IsIso p := by
  have hnonzero := unitaryJacquetPart_ne_bot_of_semisimple_induction_quotient
    hG p l r hp hl hr hmul ha π σ hπ hsemisimple hπtemp hσtemp F hF
  obtain ⟨c, _⟩ := hπsquare.2
  have hchar : π.HasCentralCharacter c.character := c.acts
  by_contra hproper
  exact hnonzero
    ((hcriterion k G hG haar π c.character hπtemp hchar).mp hπsquare
      P M U A p l r a hp hl hr hmul ha hproper)

end

end Langlands.Aubert.General.RepresentedParabolic
