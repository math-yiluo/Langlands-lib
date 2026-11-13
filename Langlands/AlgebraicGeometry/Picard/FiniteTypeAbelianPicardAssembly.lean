import Langlands.AbelianScheme.AffineUnitScheme
import Langlands.AlgebraicGeometry.Picard.RigidifiedEtaleFppfClassSheaf
import Langlands.AlgebraicGeometry.Picard.AbelianPicardSheafSeparated
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof
import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismEtaleAtlasProof
import Langlands.AlgebraicGeometry.Picard.EtaleFppfAtlasTransport
import Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction
import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction
import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof

/-! # Assembling the Picard algebraic space of an abelian scheme from a stack atlas -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The etale Picard class sheaf of an abelian scheme is an fppf sheaf. -/
theorem etaleClassSheafPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (RelativePicard.etaleClassSheafPresheaf A.X.hom) :=
  RigidifiedLineBundle.etaleClassSheafPresheaf_isSheaf_fppf A.X.hom
    (unitSection A) (unitSection_comp A) (relativeProjection_app_isIso A)

end Langlands.AbelianScheme

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace RelativePicard

/-- Over a finite-type `ℤ`-algebra, a locally finite type stack atlas of the
Picard groupoid of an abelian scheme gives the actual fppf Picard algebraic
space together with a locally finitely presented etale scheme atlas. -/
theorem finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlas
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))
    (hA : PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas A.X.hom) :
    IsAlgebraicSpace (Spec (CommRingCat.of R)) (classSheaf A.X.hom) ∧
      ∃ (U : Over (Spec (CommRingCat.of R)))
        (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf A.X.hom),
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFinitePresentation U.hom := by
  obtain ⟨hD, hE⟩ := smoothAutomorphismEtaleAtlas _ _ A.X.hom
    (lineBundleFpqcStack.2 _ _ A.X.hom) hA
    (Langlands.AbelianScheme.hasSmoothRelativeAutomorphismSchemes A)
  obtain ⟨hS, U, a, ha, hs, hU⟩ := classSheaf_algebraicSpace_of_etale_atlas A.X.hom
    (Langlands.AbelianScheme.etaleClassSheafPresheaf_isSheaf_fppf A) hD hE
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  exact ⟨hS, U, a, ha, hs, LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hU⟩

/-- The exact target follows from a locally finite type stack atlas for the
Picard groupoid of every abelian scheme over a finite-type `ℤ`-algebra. -/
theorem finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlases
    (hA : ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
      (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
      PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas A.X.hom) :
    FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} :=
  fun R _ _ A ↦ finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlas R A (hA R A)

/-- The exact target follows from the stack atlas statement for proper flat
schemes over finite-type `ℤ`-algebras: an abelian scheme is proper and smooth,
hence flat. -/
theorem finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas
    (h : FiniteTypePicardStackAtlasStatement.{u}) :
    FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} :=
  finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlases fun R _ _ A ↦
    h R A.X inferInstance inferInstance

set_option linter.defProp false in
/-- The implication proved by `finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas`,
as a single term from the stack atlas statement to the target statement. -/
def finiteTypeAbelianPicardSheafAlgebraicSpaceOfStackAtlas :
    FiniteTypePicardStackAtlasStatement.{u} →
      FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} :=
  finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas

/-- The exact target follows from the two remaining inputs of the published versal
route to the stack atlas: formally versal families over complete local bases and
etale approximation over finite-type `ℤ`-algebras. Openness of versality is the
published `picardOpennessOfVersality`. -/
theorem finiteTypeAbelianPicardSheafAlgebraicSpace_of_versalInputs
    (hF : FiniteTypeFormalVersalBundleStatement.{u})
    (hA : CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}) :
    FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} :=
  finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas
    (PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs hF
      (versalAlgebraization_of_etaleApproximation hA) picardOpennessOfVersality)

end Langlands.AlgebraicGeometry.Picard
