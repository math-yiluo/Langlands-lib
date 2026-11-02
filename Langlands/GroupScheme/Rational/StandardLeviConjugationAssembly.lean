import Langlands.GroupScheme.Rational.StandardLeviAnnihilatorTransport
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardLeviConjugationStatement
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The conjugate image of a standard Levi under an actual relative Weyl element,
defined on every test scheme independently of a normalizer lift. -/
def standardLeviWeylConjugate
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (J : Set (characterLattice T)) (w : relativeWeylGroup i) :
    SubgroupFunctor G :=
  relativeWeylConjugateSubgroupFunctor i (standardLevi i ν J)
    (torusCentralizer_le_standardLevi i ν J) w

@[simp] theorem standardLeviWeylConjugate_mk
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (J : Set (characterLattice T)) (n : normalizerPoints i) :
    standardLeviWeylConjugate i ν J (QuotientGroup.mk n) =
      (standardLevi i ν J).comap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv :=
  rfl

/-- The Weyl-conjugate construction recovers the target standard Levi under
the exact encoded-root-set condition and explicit structural inputs. -/
theorem standardLeviWeylConjugate_eq_of_rootSubset_image
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J J' : Set (characterLattice T)}
    (hJ : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hJ' : ∃ zeta, IsStandardCocharacter i ν J' zeta)
    (n : normalizerPoints i)
    (h : relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i |
          (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i |
        (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J}) :
    standardLeviWeylConjugate i ν J' (QuotientGroup.mk n) =
      standardLevi i ν J := by
  rw [standardLeviWeylConjugate_mk,
    standardLevi_eq_comap_of_rootSubset_image i hT ν hfinite hJ hJ' n h,
    ← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id]

/-- For a split torus, existence for every standard face supplies all the
structural hypotheses needed for exact encoded-root-set conjugation. -/
theorem standardLevi_eq_comap_of_standardCocharacter_exists
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T)
    (hexists : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν J zeta)
    {J J' : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hJ' : J' ⊆ simpleRelativeRoots i ν)
    (n : normalizerPoints i)
    (h : relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i |
          (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i |
        (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J}) :
    standardLevi i ν J' =
      (standardLevi i ν J).comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom :=
  standardLevi_eq_comap_of_rootSubset_image i hT ν
    (finite_simpleRelativeRoots_of_standardCocharacter_exists i ν hT hexists)
    (hexists J hJ) (hexists J' hJ') n h

/-- Independence of the rationalized actual simple roots already suffices for
the standard-Levi conjugation clause. -/
theorem standardLevi_eq_comap_of_linearIndependent_simpleRelativeRoots
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T)
    (hΔ : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)))
    {J J' : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hJ' : J' ⊆ simpleRelativeRoots i ν)
    (n : normalizerPoints i)
    (h : relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i |
          (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i |
        (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J}) :
    standardLevi i ν J' =
      (standardLevi i ν J).comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom :=
  standardLevi_eq_comap_of_standardCocharacter_exists i hT ν
    (exists_standardCocharacter_of_linearIndependent i ν hT hΔ) hJ hJ' n h

/-- A conditional reduction of the exact general conjugation statement to the
published standard-cocharacter statement. This does not prove that premise. -/
theorem standardLeviConjugationStatement_of_standardCocharacterStatement
    (hstandard : StandardCocharacterStatement.{u}) :
    StandardLeviConjugationStatement.{u} := by
  intro k _ G hG T i hi ν hν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have hexists (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
      ∃ zeta, IsStandardCocharacter i ν J zeta :=
    (hstandard k G hG T i hi ν hν J hJ).1
  constructor
  · intro J J' hJ hJ' n h
    exact standardLevi_eq_comap_of_standardCocharacter_exists i
      hi.isSplitSubtorus.1 ν hexists hJ hJ' n h
  · intro J _ n n' h
    exact standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq i ν J n n' h

/-- The exact root-system statement suffices for the general conjugation
statement; its structural realization remains a premise of this reduction. -/
theorem standardLeviConjugationStatement_of_relativeRootSystemStatement
    (hroot : RelativeRootSystemStatement.{u}) :
    StandardLeviConjugationStatement.{u} := by
  intro k _ G hG T i hi ν hν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have hroots : HasRelativeRootSystem i := hroot k G hG T i hi
  have hexists (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
      ∃ zeta, IsStandardCocharacter i ν J zeta :=
    hroots.exists_standardCocharacter i ν hi.isSplitSubtorus.1 hν J hJ
  constructor
  · intro J J' hJ hJ' n h
    exact standardLevi_eq_comap_of_rootSubset_image i hi.isSplitSubtorus.1 ν
      (hroots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν)
      (hexists J hJ) (hexists J' hJ') n h
  · intro J _ n n' h
    exact standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq i ν J n n' h

end Langlands.GroupScheme
