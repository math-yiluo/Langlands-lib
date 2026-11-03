import Langlands.GroupScheme.Rational.RootSpanSimpleConjugacy
import Langlands.Representation.Aubert.General.RationalRootSpanCoxeterComparisons

/-! # Actual comparisons for any supplied point root-sign Coxeter system -/

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
  (cs : ActualCoxeterSystem (torusPoints i) C)

/-- Pull a supplied point system back along the representative-preserving
quotient comparison, keeping the literal simple-root labels. -/
def schemeCoxeterSystem : CoxeterSystem C (relativeWeylGroup i) :=
  cs.map (weylEquiv i hN hZ).symm

omit [Mono i.hom.hom.left] in
@[simp] theorem schemeCoxeterSystem_simple (a : SimpleRoot i ν) :
    (schemeCoxeterSystem i ν hN hZ cs).simple a =
      (weylEquiv i hN hZ).symm (cs.simple a) := rfl

omit [Mono i.hom.hom.left] in
@[simp] theorem schemeCoxeterSystem_length (w : relativeWeylGroup i) :
    (schemeCoxeterSystem i ν hN hZ cs).length w =
      cs.length (weylEquiv i hN hZ w) := by
  have h := coxeterLength_map_eq cs (schemeCoxeterSystem i ν hN hZ cs)
    (weylEquiv i hN hZ).symm (Equiv.refl _) (fun _ => rfl)
    (weylEquiv i hN hZ w)
  simpa only [MulEquiv.symm_apply_apply] using h

/-- The supplied point root-sign law is exactly the scheme root-sign law. -/
theorem schemeCoxeterSystem_rootLength
    (hLength : RootLengthComparison i ν hN hZ cs)
    (w : relativeWeylGroup i) (a : SimpleRoot i ν) :
    (schemeCoxeterSystem i ν hN hZ cs).length w <
      (schemeCoxeterSystem i ν hN hZ cs).length
        (w * (schemeCoxeterSystem i ν hN hZ cs).simple a) ↔
      schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν := by
  rw [schemeCoxeterSystem_length, schemeCoxeterSystem_length,
    map_mul, schemeCoxeterSystem_simple, MulEquiv.apply_symm_apply,
    hLength, weylCharacterAction_weylEquiv]

/-- Every supplied point generator satisfying the length law comes from the
actual reflection in its own simple root. -/
theorem schemeCoxeterSystem_isRelativeReflection_simple
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs) (a : SimpleRoot i ν) :
    IsRelativeReflection i a.val ((schemeCoxeterSystem i ν hN hZ cs).simple a) :=
  hRoots.isRelativeReflection_simple_of_rootLength hT hν _
    (schemeCoxeterSystem_rootLength i ν hN hZ cs hLength) a

/-- The actual simple-reflection action fixes every cocharacter pairing
orthogonal to its root, on the entire character lattice. -/
theorem simpleReflectionPairingInvariance_of_rootLength
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs) :
    SimpleReflectionPairingInvariance i ν hN hZ cs := by
  intro a ζ hζ χ
  have hr := schemeCoxeterSystem_isRelativeReflection_simple
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength a
  have hh := hr.latticePairing_schemeWeylCharacterAction hG hi hζ χ
  change latticePairing T
    (weylCharacterAction i hN hZ (cs.simple a) χ) ζ = latticePairing T χ ζ
  rw [← (weylEquiv i hN hZ).apply_symm_apply (cs.simple a),
    weylCharacterAction_weylEquiv]
  exact hh

/-- The positive simple-reflection conjugacy law holds for the same supplied
point system, including in a nonreduced relative root system. -/
theorem positiveSimpleReflectionComparison_of_rootLength
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs) :
    PositiveSimpleReflectionComparison i ν hN hZ cs := by
  intro w a b hpos
  obtain ⟨v, rfl⟩ := (weylEquiv i hN hZ).surjective w
  rw [weylCharacterAction_weylEquiv] at hpos ⊢
  have h := hRoots.positiveSimpleReflectionLaw_of_rootLength
    (schemeCoxeterSystem i ν hN hZ cs) hT hν
    (schemeCoxeterSystem_rootLength i ν hN hZ cs hLength) v a b hpos
  have hh := (weylEquiv i hN hZ).injective.eq_iff
    (a := v * (schemeCoxeterSystem i ν hN hZ cs).simple a * v⁻¹)
    (b := (schemeCoxeterSystem i ν hN hZ cs).simple b)
  rw [map_mul, map_mul, map_inv, schemeCoxeterSystem_simple,
    schemeCoxeterSystem_simple, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at hh
  exact hh.trans h

/-- The actual standard-Levi Weyl images agree with the standard subgroups
of every supplied system satisfying the literal root-sign length law. -/
theorem actualLeviWeylIdentification_of_rootLength
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs) :
    actualLeviWeylIdentification (torusPoints i) (levi i ν) cs :=
  actualLeviWeylIdentification_of_simplePairing i ν hN hZ cs
    hi.isSplitSubtorus.1 hRoots hν hLength
    (simpleReflectionPairingInvariance_of_rootLength i ν hN hZ cs hG hi hRoots hν hLength)

end Langlands.Aubert.General.RationalPointFamily
