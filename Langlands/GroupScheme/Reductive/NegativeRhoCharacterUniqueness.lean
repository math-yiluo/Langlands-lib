import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.Reductive.NegativeRhoCharacter

/-! # Uniqueness of the extended negative-rho character -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Extension

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
  {ν : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {i : H ⟶ G} {j : T.toGrp ⟶ G}
  (hH : (parabolic ν).IsRepresentedBy i) (hc : IsClosedSubgroup i)
  (hT : (centralizer ν).IsRepresentedBy j)

/-- All parabolic characters, identified with the character lattice of the
supplied commutative dynamic centralizer. -/
def parabolicCharacterLatticeEquiv : rationalCharacters H ≃+ characterLattice T :=
  (parabolicCharacterEquiv hH hc hT).trans (rationalCharacters.equivCharacterLattice T)

/-- The existing extension is exactly the inverse restriction equivalence. -/
theorem parabolicCharacterLatticeEquiv_symm_eq :
    (parabolicCharacterLatticeEquiv hH hc hT).symm.toAddMonoidHom =
      extendCentralizerCharacter hH hT :=
  rfl

include hc in
/-- Every rational character of a closed dynamic parabolic is the extension
of its restriction to the centralizer. -/
theorem character_eq_extendCentralizerCharacter (χ : rationalCharacters H) :
    χ = extendCentralizerCharacter hH hT
      (rationalCharacters.equivCharacterLattice T
        (characterRestrict (centralizerToParabolic hH hT) χ)) :=
  ((parabolicCharacterLatticeEquiv hH hc hT).symm_apply_apply χ).symm

include hc in
/-- The limit extension gives every rational character of the closed parabolic. -/
theorem extendCentralizerCharacter_surjective :
    Function.Surjective (extendCentralizerCharacter hH hT) :=
  (parabolicCharacterLatticeEquiv hH hc hT).symm.surjective

end Extension

section NegativeRho

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {i : H ⟶ G} {j : T.toGrp ⟶ G}
  (hH : (parabolic ν).IsRepresentedBy i) (hc : IsClosedSubgroup i)
  (hT : (centralizer ν).IsRepresentedBy j)
  {J : Type v} (Q : RootDatum J (characterLattice T) (cocharacterLattice T))
  (b : Q.Base) (hspan : Q.corootSpan ℤ = ⊤)

include hc in
/-- A character is the actual extended negative rho exactly when its
restriction is negative rho on the supplied centralizer. -/
theorem eq_negativeRhoCharacter_iff (χ : rationalCharacters H) :
    χ = negativeRhoCharacter hH hT Q b hspan ↔
      rationalCharacters.equivCharacterLattice T
        (characterRestrict (centralizerToParabolic hH hT) χ) =
          -IntegralWeylVector.rho Q b hspan := by
  constructor
  · rintro rfl
    exact restrict_negativeRhoCharacter hH hT Q b hspan
  · intro hχ
    apply (character_eq_iff_restrict_eq hH hc hT _ _).mpr
    apply (rationalCharacters.equivCharacterLattice T).injective
    rw [restrict_negativeRhoCharacter]
    exact hχ

end NegativeRho

end Langlands.GroupScheme.Dynamic
