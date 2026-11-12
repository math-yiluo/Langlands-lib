import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof

/-!
# The Galois-twisted line as an algebraic space

The quotient of the line `Spec K'[X]`, viewed over `Spec K`, by the étale equivalence relation
`GaloisTwistedLine.relation`. It is the fppf sheaf quotient of the slice relation
(`RelationQuotient.quotientSheaf`), with the quotient map from the line as its atlas, exactly as
in the Library's proof of Stacks 02WW. Keeping the explicit sheaf quotient gives access to the
local surjectivity of the quotient map and to its kernel pair.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

open RelationQuotient KernelPair

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

variable (K K') in
/-- The line as a scheme over `Spec K`. -/
abbrev lineOver : Over (Spec (CommRingCat.of K)) := Over.mk (lineBase (K := K) (K' := K'))

/-- The relation as a scheme over `Spec K`. -/
abbrev relOver : Over (Spec (CommRingCat.of K)) := Over.mk ((relation D).t ≫ lineBase)

/-- The first projection over `Spec K`. -/
abbrev tOver : relOver D ⟶ lineOver K K' := Over.homMk (relation D).t

/-- The second projection over `Spec K`. -/
abbrev sOver : relOver D ⟶ lineOver K K' :=
  Over.homMk (relation D).s (tMap_lineBase D).symm

theorem isOverEquivRel : IsOverEquivRel (tOver D) (sOver D) :=
  (relation D).isOverEquivRel lineBase (tMap_lineBase D)

theorem isPullback_quotient :
    IsPullback ((schemeYoneda _).map (tOver D)) ((schemeYoneda _).map (sOver D))
      (quotientMap (tOver D) (sOver D)) (quotientMap (tOver D) (sOver D)) :=
  isPullback_quotientMap (isOverEquivRel D)

theorem locallyOfFiniteType_tOver : LocallyOfFiniteType (tOver D).left := by
  have := (relation D).etale_t
  exact inferInstanceAs (LocallyOfFiniteType (relation D).t)

theorem hasRepresentableDiagonal_quotient :
    HasRepresentableDiagonal (quotientSheaf (tOver D) (sOver D)).obj :=
  hasRepresentableDiagonal_of_isPullback
    LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent
    (quotientMap (tOver D) (sOver D)) (isPullback_quotient D) (locallyOfFiniteType_tOver D)

theorem isEtale_quotientMap : IsEtale (quotientMap (tOver D) (sOver D)) := by
  have := (relation D).etale_s
  exact isEtale_of_isPullback (quotientMap (tOver D) (sOver D))
    (hasRepresentableDiagonal_quotient D) (isPullback_quotient D)
    (inferInstanceAs (Etale (relation D).s))

theorem isSurjective_quotientMap : IsSurjective (quotientMap (tOver D) (sOver D)) :=
  OpenSubfunctorImages.isSurjective_of_isEtale_isLocallySurjective _ (isEtale_quotientMap D)
    inferInstance

/-- **The Galois-twisted line**, an algebraic space over `Spec K`. -/
def space : AlgebraicSpace (Spec (CommRingCat.of K)) :=
  ⟨quotientSheaf (tOver D) (sOver D), hasRepresentableDiagonal_quotient D, lineOver K K',
    quotientMap (tOver D) (sOver D), isEtale_quotientMap D, isSurjective_quotientMap D⟩

/-- The atlas of the Galois-twisted line by the line. -/
def atlas : (schemeYoneda _).obj (lineOver K K') ⟶ (space D).presheaf :=
  quotientMap (tOver D) (sOver D)

theorem atlas_isEtale : IsEtale (atlas D) := isEtale_quotientMap D

theorem atlas_isSurjective : IsSurjective (atlas D) := isSurjective_quotientMap D

theorem isPullback_atlas :
    IsPullback ((schemeYoneda _).map (tOver D)) ((schemeYoneda _).map (sOver D))
      (atlas D) (atlas D) :=
  isPullback_quotient D

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
