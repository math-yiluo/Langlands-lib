import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.GroupScheme.HopfBaseChange
import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent

/-! # Actual diagonalizable reductions and coordinate bialgebra presentations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A diagonalizable actual group is affine over its base. -/
theorem isAffineHom_of_isDiagonalizable {S : Scheme.{u}} {H : GroupScheme S}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) : IsAffineHom H.X.hom := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := hH
  have : IsAffineHom (Diagonalizable.groupScheme
      (CommRingCat.of (ULift.{u} ℤ)) N).X.hom := Diagonalizable.isAffineHom _ _
  have hd : IsAffineHom (RelativeMultiplicativeType.diagonalizable S N).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ ‹_›
  have : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- A group over an affine base is affine whenever a flat surjective affine
base change is diagonalizable. -/
theorem isAffine_of_diagonalizable_baseChange {R : CommRingCat.{u}}
    (H : GroupScheme (Spec R)) {S' : Scheme.{u}} [IsAffine S']
    (p : S' ⟶ Spec R) [Flat p] [Surjective p]
    (hH : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H)) :
    IsAffine H.X.left := by
  have : IsAffineHom ((GroupScheme.baseChange p).obj H).X.hom :=
    isAffineHom_of_isDiagonalizable hH
  have hP : IsAffine ((GroupScheme.baseChange p).obj H).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange p).obj H).X.hom
  change IsAffine (CategoryTheory.Limits.pullback H.X.hom p) at hP
  exact Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent.isAffine_of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback H.X.hom p)

/-- The finite étale splitting hypothesis supplies the affine instance needed
to form the coordinate Hopf algebra of the source. -/
theorem isAffine_of_finiteEtaleSplit {R : CommRingCat.{u}}
    (H : GroupScheme (Spec R))
    (hH : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec R),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H)) :
    IsAffine H.X.left := by
  obtain ⟨S', p, hfin, het, hsurj, hdiag⟩ := hH
  let : IsFinite p := hfin
  let : Etale p := het
  let : Surjective p := hsurj
  let : IsAffine S' := isAffine_of_isAffineHom p
  exact isAffine_of_diagonalizable_baseChange H p hdiag

/-- An actual finite-character group-algebra presentation of a coordinate Hopf
algebra. -/
structure DiagonalizableHopfPresentation (R : CommRingCat.{u})
    (C : CommHopfAlgCat.{u} R) where
  Characters : Type u
  [addCommGroup : AddCommGroup Characters]
  fg : AddGroup.FG Characters
  equiv : C ≃ₐc[R] AddMonoidAlgebra R Characters

attribute [instance] DiagonalizableHopfPresentation.addCommGroup
  DiagonalizableHopfPresentation.fg

/-- A diagonalizable actual Hopf spectrum gives a bialgebra equivalence of its
coordinates with the group algebra of a finitely generated abelian group. -/
def hopfPresentationOfIsDiagonalizable {R : CommRingCat.{u}}
    (C : CommHopfAlgCat.{u} R)
    (hC : RelativeMultiplicativeType.IsDiagonalizable ((hopfSpec R).obj (op C))) :
    DiagonalizableHopfPresentation R C := by
  classical
  apply Classical.choice
  obtain ⟨N, _, hfg, ⟨e⟩⟩ := hC
  let e' := e ≪≫ (Diagonalizable.relativeModelIso R N).symm ≪≫
    (Diagonalizable.hopfSpecIso R N).symm
  let i : Diagonalizable.hopfAlgebra R N ≅ C :=
    (hopfSpec.fullyFaithful.preimageIso e').unop
  exact ⟨{
    Characters := N
    fg := hfg
    equiv := (CommHopfAlgCat.ofIso i).symm }⟩

/-- The scalar-extended coordinate Hopf spectrum recovers the actual
base-changed affine group. -/
def affineScalarExtensionIso {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left] :
    (hopfSpec (CommRingCat.of S)).obj
        (op (HopfCoordinates.scalarExtension R S (AffineCoordinates.hopfAlgebra G))) ≅
      (GroupScheme.baseChange (Spec.algebraMap R S)).obj G :=
  (HopfCoordinates.baseChangeSpecIso R S (AffineCoordinates.hopfAlgebra G)).symm ≪≫
    (GroupScheme.baseChange (Spec.algebraMap R S)).mapIso (AffineCoordinates.hopfSpecIso G)

/-- A diagonalizable actual base change gives a presentation of the
scalar-extended coordinate Hopf algebra. -/
def diagonalizableScalarPresentation {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R S)).obj G)) :
    DiagonalizableHopfPresentation (CommRingCat.of S)
      (HopfCoordinates.scalarExtension R S (AffineCoordinates.hopfAlgebra G)) :=
  hopfPresentationOfIsDiagonalizable _
    (RelativeMultiplicativeType.IsDiagonalizable.of_iso (affineScalarExtensionIso G) hG)

/-- Extract the actual scalar-reduction bialgebra presentation from a
diagonalizable group-scheme reduction. -/
def diagonalizableReductionPresentation {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    (J : Ideal R)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G)) :
    DiagonalizableHopfPresentation (CommRingCat.of (R ⧸ J))
      (HopfCoordinates.scalarExtension R (R ⧸ J) (AffineCoordinates.hopfAlgebra G)) :=
  diagonalizableScalarPresentation G hG

/-- An actual group-algebra presentation of the coordinates supplies an actual
diagonalizable group-scheme isomorphism, preserving the character group. -/
def diagonalizableIsoOfCoordinates {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    (N : Type u) [AddCommGroup N]
    (e : AffineCoordinates.hopfAlgebra G ≃ₐc[R] AddMonoidAlgebra R N) :
    G ≅ (Diagonalizable.groupScheme R N).toGrp :=
  (AffineCoordinates.isoOfBialgEquiv G (Diagonalizable.hopfAlgebra R N) e).symm ≪≫
    Diagonalizable.hopfSpecIso R N

/-- Finite generation of the supplied coordinate character group gives
diagonalizability in the relative convention. -/
theorem isDiagonalizable_of_coordinates {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    (N : Type u) [AddCommGroup N] [AddGroup.FG N]
    (e : AffineCoordinates.hopfAlgebra G ≃ₐc[R] AddMonoidAlgebra R N) :
    RelativeMultiplicativeType.IsDiagonalizable G :=
  RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (diagonalizableIsoOfCoordinates G N e) (Diagonalizable.isDiagonalizable_groupScheme R N)

end Langlands.GroupScheme.CompleteLocalDeformation
