import Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismEtaleAtlasStatement
import Langlands.AlgebraicGeometry.Picard.FieldSmoothAutomorphisms
import Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement
import Langlands.AlgebraicGeometry.Picard.EtaleFppfAtlasTransport

/-! # Assembling an actual fppf Picard atlas from the stack inputs -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace RelativePicard

/-- The actual Picard stack inputs give an etale class-sheaf diagonal and
atlas, using the proved fpqc stack and smooth field automorphism results. -/
theorem fieldEtalePicardAtlas_of_stackInputs
    (hA : FieldPicardStackAtlasStatement.{u})
    (hQ : SmoothAutomorphismEtaleAtlasStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    HasRepresentableDiagonal (etaleClassSheafPresheaf X.hom) ∧
      ∃ (U : Over (Spec (CommRingCat.of k)))
        (a : (schemeYoneda _).obj U ⟶ etaleClassSheafPresheaf X.hom),
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom := by
  let : IsProper X.hom := hX
  exact hQ _ _ X.hom (lineBundleFpqcStack.2 _ _ X.hom) (hA k X hX)
    (PicardGroupoid.field_hasSmoothRelativeAutomorphismSchemes X.hom)

/-- Full fppf Picard algebraicity and a locally finite type etale atlas
follow from the stack atlas, smooth quotient and topology comparison inputs. -/
theorem fieldPicardAlgebraicSpaceAtlas_of_stackInputs
    (hA : FieldPicardStackAtlasStatement.{u})
    (hQ : SmoothAutomorphismEtaleAtlasStatement.{u})
    (hT : FieldEtaleFppfClassSheafStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    IsAlgebraicSpace (Spec (CommRingCat.of k)) (classSheaf X.hom) ∧
      ∃ (U : Over (Spec (CommRingCat.of k)))
        (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom),
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom := by
  obtain ⟨hD, hU⟩ := fieldEtalePicardAtlas_of_stackInputs hA hQ k X hX
  exact classSheaf_algebraicSpace_of_etale_atlas X.hom (hT k X hX) hD hU

/-- A chosen actual scheme atlas of the full fppf Picard sheaf, retaining
the three unproved stack-atlas, quotient and comparison inputs explicitly. -/
def fieldFppfPicardAtlas
    (hA : FieldPicardStackAtlasStatement.{u})
    (hQ : SmoothAutomorphismEtaleAtlasStatement.{u})
    (hT : FieldEtaleFppfClassSheafStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    Σ (U : Over (Spec (CommRingCat.of k))),
      {a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom //
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom} :=
  let hex := (fieldPicardAlgebraicSpaceAtlas_of_stackInputs hA hQ hT k X hX).2
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

end Langlands.AlgebraicGeometry.Picard
