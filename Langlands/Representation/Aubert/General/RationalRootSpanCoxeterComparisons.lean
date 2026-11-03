import Langlands.GroupScheme.Rational.RelativeRootCoxeterConstruction
import Langlands.GroupScheme.Rational.RelativeReflectionPairing
import Langlands.Representation.Aubert.General.RationalCoxeterTransport
import Langlands.Representation.Aubert.General.RationalPointLeviWeylIdentification

/-! # Actual point comparisons from root-span Coxeter reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))

/-- The root-sign length law transports without any full-character realization. -/
theorem pointCoxeterSystem_rootLengthComparison_of_rootLength
    (hLength : ∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
      cs.length w < cs.length (w * cs.simple a) ↔
        schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν) :
    RootLengthComparison i ν hN hZ (pointCoxeterSystem i ν hN hZ cs) := by
  intro w a
  obtain ⟨v, rfl⟩ := (weylEquiv i hN hZ).surjective w
  simpa only [pointCoxeterSystem_simple, ← map_mul,
    pointCoxeterSystem_length, weylCharacterAction_weylEquiv] using hLength v a

/-- Root-span simple reflections supply the whole-character point pairing law. -/
theorem pointCoxeterSystem_simplePairing_of_reflections
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a)) :
    SimpleReflectionPairingInvariance i ν hN hZ
      (pointCoxeterSystem i ν hN hZ cs) := by
  intro a ζ hζ χ
  change latticePairing T
    (weylCharacterAction i hN hZ
      (weylEquiv i hN hZ (cs.simple a)) χ) ζ = latticePairing T χ ζ
  rw [weylCharacterAction_weylEquiv]
  exact (hSimple a).latticePairing_schemeWeylCharacterAction hG hi hζ χ

/-- A given actual relative root system gives a finite point Coxeter system
with root-sign length and the exact actual standard-Levi Weyl identification. -/
theorem exists_rootSpanPointCoxeterSystem
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν) :
    Finite (Weyl i) ∧ Finite (SimpleRoot i ν) ∧
      ∃ (C : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ cs ∧
        SimpleReflectionPairingInvariance i ν hN hZ cs ∧
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs := by
  obtain ⟨hW, hA, C, cs, hSimple, hLength⟩ :=
    hRoots.exists_rootSpanCoxeterSystem hi.isSplitSubtorus.1 hν
  have hLength' := pointCoxeterSystem_rootLengthComparison_of_rootLength
    i ν hN hZ cs hLength
  have hFix := pointCoxeterSystem_simplePairing_of_reflections
    i ν hN hZ cs hG hi hSimple
  refine ⟨Finite.of_equiv _ (weylEquiv i hN hZ).toEquiv, hA, C,
    pointCoxeterSystem i ν hN hZ cs, hLength', hFix, ?_⟩
  exact actualLeviWeylIdentification_of_simplePairing i ν hN hZ _
    hi.isSplitSubtorus.1 hRoots hν hLength' hFix

/-- Finite actual point Coxeter data with its proved length, pairing and
standard-Levi Weyl comparisons. -/
structure RootSpanPointCoxeterData where
  finiteWeyl : Finite (Weyl i)
  finiteSimple : Finite (SimpleRoot i ν)
  matrix : CoxeterMatrix (SimpleRoot i ν)
  system : ActualCoxeterSystem (torusPoints i) matrix
  rootLength : RootLengthComparison i ν hN hZ system
  simplePairing : SimpleReflectionPairingInvariance i ν hN hZ system
  leviWeyl : actualLeviWeylIdentification (torusPoints i) (levi i ν) system

/-- Choose the actual point Coxeter data constructed from the given actual
relative-root-system witness. -/
def rootSpanPointCoxeterData
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν) :
    RootSpanPointCoxeterData i ν hN hZ := by
  apply Classical.choice
  obtain ⟨hW, hA, C, cs, hLength, hFix, hIdent⟩ :=
    exists_rootSpanPointCoxeterSystem i ν hN hZ hG hi hRoots hν
  exact ⟨⟨hW, hA, C, cs, hLength, hFix, hIdent⟩⟩

end Langlands.Aubert.General.RationalPointFamily
