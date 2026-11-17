import Langlands.Geometry.Analytic.SmallFiniteProductNeighborhoods
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesStatement

/-! # Actual small etale projection from target locality and the finite-pieces criterion -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
  (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
  [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]

/-- The actual second projection has etale finite pieces at every actual
quotient point, under the general target-local finiteness criterion. -/
theorem recognitionSmallSnd_hasFiniteEtalePieces
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsEtaleAllPieces) (t : (recognitionSmallProductPresentation f g).space) :
    (recognitionSmallSnd f g).saturationExtension.HasFinitePiecesAt
      (fun _ _ a s => a.IsEtaleAtPoint s) t := by
  let raw := (recognitionProductShrink f g).symm t
  let y := FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap raw
  let z := FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap raw
  have hindex : Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap) := by
    obtain ⟨i, -⟩ := (recognitionSmallProductPresentation f g).atlas.exists_mem_range_chart t
    exact ⟨(equivShrink (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)).symm i⟩
  let _ := hindex
  let N := etaleFiniteProductNeighborhood (f := f) (g := g) (y := y) (z := z) (hf y)
    (FibreProduct.baseMap_fst f.compatibleRecognitionMap g.compatibleRecognitionMap raw)
  exact N.smallSnd_hasFiniteEtalePieces hlocal hpush htensor t rfl rfl

/-- The missing general criteria are explicit inputs. Together they make
the existing actual small projection etale over every recognized piece,
with no nonempty-space or separation hypothesis on the total product. -/
theorem recognitionSmallSnd_isEtaleAllPieces
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsEtaleAllPieces) :
    (recognitionSmallSnd f g).saturationExtension.IsEtaleAllPieces := by
  have hall : ∀ t : (recognitionSmallProductPresentation f g).space,
      (recognitionSmallSnd f g).saturationExtension.HasAllPiecesAt
        (fun _ _ a s => a.IsEtaleAtPoint s) t :=
    fun t => hupgrade (recognitionSmallProductPresentation f g) g.recognitionSource
      (recognitionSmallSnd f g).saturationExtension t
        (recognitionSmallSnd_hasFiniteEtalePieces f g hlocal hpush htensor hf t)
  intro t
  exact ⟨univ, isOpen_univ, mem_univ t,
    fun x _ => hasAllPiecesAt_isEtaleAtPoint_iff.mp (hall x)⟩

/-- The certified morphism is exactly the existing complete canonical
small projection; the two general analytic criteria remain explicit. -/
def etaleRecognitionSmallSnd
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsEtaleAllPieces) :
    {q : StrongHom (recognitionSmallProductPresentation f g).saturatedPresentation
      g.recognitionSource.saturatedPresentation // q.IsEtaleAllPieces} :=
  ⟨(recognitionSmallSnd f g).saturationExtension,
    recognitionSmallSnd_isEtaleAllPieces f g hlocal hupgrade hpush htensor hf⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
