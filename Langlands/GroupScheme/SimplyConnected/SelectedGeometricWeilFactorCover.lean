import Langlands.GroupScheme.SimplyConnected.PrescribedWeilFactorCover

/-! # Actual Weil covers for a selected geometric almost-simple factor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme
namespace SimplyConnectedAlmostSimpleProduct

section StabilizerModel

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {A : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj A).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj A).X.hom]
  (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj A))
  [IsGalois k L] [IsAffineHom A.X.hom]
  [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] [LocallyOfFinitePresentation A.X.hom]
  [IsSepClosed L]

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

/-- The canonical embedding-product comparison for the actual selected
stabilizer-field model, before descent to the ground field. -/
def stabilizerEmbeddingProductIso (j : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj
      (AffineWeil.groupScheme k (D.factorStabilizerField j) (D.factorStabilizerDescent j).1) ≅
        pi (D.embeddingConjugateFamily j) := by
  have hs : ∀ x : D.factorStabilizerField j,
      ((minpoly k x).map (algebraMap k L)).Splits :=
    fun x => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable k x)
  let hb := Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement
    k (D.factorStabilizerField j) L hs
  exact AffineWeil.embeddingProductIsoOfBijective k (D.factorStabilizerField j) L hb
    (D.factorStabilizerDescent j).1

/-- The selected embedding comparison commutes with every full ground-field
Galois automorphism and the original embedding-coordinate transport. -/
theorem stabilizerEmbeddingProductIso_descent (j : D.Index) (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map (D.stabilizerEmbeddingProductIso j).hom ≫
        (EmbeddingProduct.galoisIso (D.factorStabilizerDescent j).1 σ).hom =
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ)
        (AffineWeil.groupScheme k (D.factorStabilizerField j)
          (D.factorStabilizerDescent j).1)).hom ≫ (D.stabilizerEmbeddingProductIso j).hom := by
  have hs : ∀ x : D.factorStabilizerField j,
      ((minpoly k x).map (algebraMap k L)).Splits :=
    fun x => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable k x)
  let hb := Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement
    k (D.factorStabilizerField j) L hs
  have hp := AffineWeil.embeddingProductIsoOfBijective_descent k (D.factorStabilizerField j)
    L hb (D.factorStabilizerDescent j).1
  simpa only [stabilizerEmbeddingProductIso] using hp σ

/-- An actual almost-simple group is the Weil restriction of precisely the
selected geometric factor's stabilizer-field model. -/
def stabilizerWeilIso (hA : IsAlmostSimple A) (j : D.Index) :
    A ≅ AffineWeil.groupScheme k (D.factorStabilizerField j) (D.factorStabilizerDescent j).1 :=
  D.weilRestrictionIsoOfCompatibleEmbeddingProduct hA j (D.stabilizerEmbeddingProductIso j)
    (D.stabilizerEmbeddingProductIso_descent j)

/-- After scalar extension, the inverse Weil presentation is exactly the
canonical embedding-product comparison followed by the original selected
conjugate-factor product isomorphism. -/
theorem stabilizerWeilIso_baseChange_inv (hA : IsAlmostSimple A) (j : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).map (D.stabilizerWeilIso hA j).inv =
      (D.stabilizerEmbeddingProductIso j).hom ≫ (D.embeddingConjugateProductIso hA j).hom :=
  D.weilRestrictionIsoOfCompatibleEmbeddingProduct_baseChange_inv hA j
    (D.stabilizerEmbeddingProductIso j) (D.stabilizerEmbeddingProductIso_descent j)

end StabilizerModel

section Cover

variable {k : Type u} [Field k]
  {C : GroupScheme (Spec (CommRingCat.of k))} (Dk : SimplyConnectedAlmostSimpleProduct C)

private instance selectedGeometric_factorAffine (i : Dk.Index) :
    IsAffineHom (Dk.factor i).X.hom :=
  (Dk.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

private instance selectedGeometric_factorSmooth (i : Dk.Index) : Smooth (Dk.factor i).X.hom :=
  (Dk.isSimplyConnected i).isSemisimple.isConnectedReductive.smooth

private instance selectedGeometric_affineBaseChange {k L : Type u}
    [Field k] [Field L] [Algebra k L]
    {A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom A.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj A).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd A.X.hom _)
  infer_instance

private instance selectedGeometric_smoothBaseChange {k L : Type u}
    [Field k] [Field L] [Algebra k L]
    {A : GroupScheme (Spec (CommRingCat.of k))} [Smooth A.X.hom] :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj A).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd A.X.hom _)
  infer_instance

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

/-- An actual covering product using the exact stabilizer field and descended
group of a specified geometric factor of the prescribed ground-field factor. -/
def weilFactorAtGeometricIndex (hC : IsSimplyConnected C) (i : Dk.Index)
    (Dgeo : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj (Dk.factor i)))
    (j : Dgeo.Index) : SimplyConnectedWeilFactor (Dk.inclusion i) := by
  let E := Dgeo.factorStabilizerField j
  let H := (Dgeo.factorStabilizerDescent j).1
  have hH : IsSimplyConnected H := Dgeo.isSimplyConnected_factorStabilizerDescent j
  let : IsAffineHom H.X.hom := hH.isSemisimple.isConnectedReductive.isAffineHom
  exact Dk.weilFactorOfIso E H hC i hH
    (Dgeo.isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed j)
    (Dgeo.stabilizerWeilIso (Dk.isAlmostSimple i) j)

@[simp] theorem weilFactorAtGeometricIndex_extension (hC : IsSimplyConnected C) (i : Dk.Index)
    (Dgeo : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj (Dk.factor i)))
    (j : Dgeo.Index) :
    (Dk.weilFactorAtGeometricIndex hC i Dgeo j).extension = Dgeo.factorStabilizerField j := rfl

@[simp] theorem weilFactorAtGeometricIndex_factor (hC : IsSimplyConnected C) (i : Dk.Index)
    (Dgeo : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj (Dk.factor i)))
    (j : Dgeo.Index) :
    (Dk.weilFactorAtGeometricIndex hC i Dgeo j).factor = (Dgeo.factorStabilizerDescent j).1 := rfl

end Cover
end SimplyConnectedAlmostSimpleProduct
end Langlands.GroupScheme
