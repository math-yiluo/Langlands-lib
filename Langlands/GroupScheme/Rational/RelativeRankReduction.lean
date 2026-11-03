import Langlands.GroupScheme.Rational.RelativeRankAssembly
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Intrinsic rank reduction to three independent geometric statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Lift

variable [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} {a : A.toGrp ⟶ G}

/-- A chosen actual factorization of a central split torus through a prescribed
maximal split torus, using the published product/image factorization. -/
def IsMaximalSplitTorus.centralSplitTorusLift (hi : IsMaximalSplitTorus i)
    (ha : IsCentralSplitTorus a) : A.toGrp ⟶ T.toGrp :=
  (ha.exists_factor_of_isMaximalSplitTorus (j := 𝟙 G) (t := i)
    (IsClosedSubgroup.of_iso (Iso.refl G)) (by simpa using hi)).choose

@[reassoc (attr := simp)]
theorem IsMaximalSplitTorus.centralSplitTorusLift_comp (hi : IsMaximalSplitTorus i)
    (ha : IsCentralSplitTorus a) : hi.centralSplitTorusLift ha ≫ i = a :=
  (ha.exists_factor_of_isMaximalSplitTorus (j := 𝟙 G) (t := i)
    (IsClosedSubgroup.of_iso (Iso.refl G)) (by simpa using hi)).choose_spec

end Lift

/-- Integral restriction injectivity on split components implies integral
restriction injectivity on every maximal split torus. -/
theorem characterRestrict_injective_of_characterRestriction
    (hrestriction : CharacterRestrictionStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    Function.Injective (characterRestrict i) := by
  have := hG.isAffineHom
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  have ha_inj := (hrestriction k G hG A a ha).1
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  apply ha_inj
  rw [map_zero, ← hi.centralSplitTorusLift_comp ha.isCentralSplitTorus,
    characterRestrict_comp, AddMonoidHom.comp_apply, hχ, map_zero]

/-- Tensoring the preceding integral injection with the flat module `ℚ` gives
injectivity of the actual rationalized restriction to every maximal split torus. -/
theorem rationalCharacterRestrictRat_injective_of_characterRestriction
    (hrestriction : CharacterRestrictionStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    Function.Injective (rationalCharacterRestrictRat i) :=
  rationalization_injective (characterRestrict i)
    (characterRestrict_injective_of_characterRestriction hrestriction hG hi)

/-- Conditional assembly of the exact published rank proposition from the three
independent geometric statements. This theorem does not prove those premises. -/
theorem relativeRankIdentityStatement_of_complement_restriction_conjugacy
    (hcompl : RelativeCharacterRootComplementStatement.{u})
    (hrestriction : CharacterRestrictionStatement.{u})
    (hconjugacy : MaximalSplitTorusConjugacyStatement.{u}) :
    RelativeRankIdentityStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have hT := hi.isSplitSubtorus.1
  have hinj := rationalCharacterRestrictRat_injective_of_characterRestriction hrestriction hG hi
  have hsum := splitTorusRank_eq_relativeRootRank_add_rationalCharacterRank i hT
    (hcompl k G hG T i hi).1 hinj
  refine ⟨hT.finite_characterLatticeRat, hT.finite_relativeRootSpan i,
    hG.finite_rationalCharactersRat,
    splitRank_eq_splitTorusRank_of_conjugacyStatement hconjugacy hG i hi, hsum, ?_⟩
  intro A a ha
  obtain ⟨hbij, hrank⟩ :=
    rationalCharacterRestrictRat_consequences_of_characterRestriction hrestriction hG ha
  exact ⟨ha.isCentralSplitTorus.isSplitSubtorus.1.finite_characterLatticeRat,
    hbij, hrank, hsum.trans (congrArg (fun n => relativeRootRank i + n) hrank)⟩

end Langlands.GroupScheme
