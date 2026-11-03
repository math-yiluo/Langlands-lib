import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy
import Langlands.Representation.Aubert.General.RationalLeviWeylComparison
import Langlands.Representation.Aubert.General.RationalRootSignTarget

/-! # Transport of a scheme relative Coxeter system to the actual point quotient -/

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

/-- Transport through the representative-preserving full-centralizer quotient
comparison, with the literal simple-root labels unchanged. -/
def pointCoxeterSystem : ActualCoxeterSystem (torusPoints i) C :=
  cs.map (weylEquiv i hN hZ)

omit [Mono i.hom.hom.left] in
@[simp] theorem pointCoxeterSystem_simple (a : SimpleRoot i ν) :
    (pointCoxeterSystem i ν hN hZ cs).simple a =
      weylEquiv i hN hZ (cs.simple a) :=
  rfl

omit [Mono i.hom.hom.left] in
/-- Length is preserved by the published generator-preserving transport lemma. -/
@[simp] theorem pointCoxeterSystem_length (w : relativeWeylGroup i) :
    (pointCoxeterSystem i ν hN hZ cs).length (weylEquiv i hN hZ w) =
      cs.length w :=
  coxeterLength_map_eq cs (pointCoxeterSystem i ν hN hZ cs)
    (weylEquiv i hN hZ) (Equiv.refl _) (fun _ => rfl) w

/-- A scheme root-sign realization supplies the actual point length comparison. -/
theorem pointCoxeterSystem_rootLengthComparison
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) :
    RootLengthComparison i ν hN hZ (pointCoxeterSystem i ν hN hZ cs) := by
  intro w a
  obtain ⟨v, rfl⟩ := (weylEquiv i hN hZ).surjective w
  simpa only [pointCoxeterSystem_simple, ← map_mul,
    pointCoxeterSystem_length, weylCharacterAction_weylEquiv] using hcs.2.2.1 v a

omit [Mono i.hom.hom.left] in
/-- Standard subgroups transport through the same quotient equivalence. -/
theorem pointCoxeterSystem_standardSubgroup (I : Finset (SimpleRoot i ν)) :
    standardSubgroup (pointCoxeterSystem i ν hN hZ cs) I =
      (standardSubgroup cs I).map (weylEquiv i hN hZ).toMonoidHom := by
  unfold standardSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨cs.simple a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- The realization's scheme standard-subgroup clause gives the required
identification with the range of the actual Levi Weyl inclusion. -/
theorem pointCoxeterSystem_actualLeviWeylIdentification
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) :
    actualLeviWeylIdentification (torusPoints i) (levi i ν)
      (pointCoxeterSystem i ν hN hZ cs) := by
  intro I
  rw [pointCoxeterSystem_standardSubgroup, hcs.2.2.2.2 I]
  exact (weylEquiv_map_schemeStandardWeyl i ν hN hZ I).symm

/-- The positive reflection-label criterion holds for the transported system,
including for nonreduced root systems. -/
theorem pointCoxeterSystem_positiveSimpleReflectionComparison
    [Finite (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) :
    PositiveSimpleReflectionComparison i ν hN hZ
      (pointCoxeterSystem i ν hN hZ cs) := by
  intro w a b hpos
  obtain ⟨v, rfl⟩ := (weylEquiv i hN hZ).surjective w
  rw [weylCharacterAction_weylEquiv] at hpos
  simpa only [pointCoxeterSystem_simple, ← map_inv, ← map_mul,
    (weylEquiv i hN hZ).injective.eq_iff, weylCharacterAction_weylEquiv]
    using hcs.conj_simple_iff hT v a b hpos

/-- The two root-sign assertions and the actual Levi Weyl identification are
available for one and the same transported system. -/
theorem pointCoxeterSystem_comparisons
    [Finite (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) :
    RootLengthComparison i ν hN hZ (pointCoxeterSystem i ν hN hZ cs) ∧
      PositiveSimpleReflectionComparison i ν hN hZ
        (pointCoxeterSystem i ν hN hZ cs) ∧
      actualLeviWeylIdentification (torusPoints i) (levi i ν)
        (pointCoxeterSystem i ν hN hZ cs) :=
  ⟨pointCoxeterSystem_rootLengthComparison i ν hN hZ cs hcs,
    pointCoxeterSystem_positiveSimpleReflectionComparison i ν hN hZ cs hT hcs,
    pointCoxeterSystem_actualLeviWeylIdentification i ν hN hZ cs hcs⟩

end Langlands.Aubert.General.RationalPointFamily
