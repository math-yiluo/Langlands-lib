import Langlands.Geometry.Analytic.EtaleBaseChangeStatement
import Langlands.Geometry.Analytic.AnalyticFibreProductStatement
import Langlands.Geometry.Analytic.ConditionalLocalizedEtalePullback
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityOfDescent
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof

/-! # Étale base change along glued fibre products from localized étale pullbacks -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- If one pullback square of a cospan has an étale second projection, then so does every
pullback square of the same cospan: the two squares are related by an isomorphism of their
top-left corners over the second projections, and `etale` respects isomorphisms. -/
theorem etale_snd_of_isPullback {P P' A B X : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B} {p' : P' ⟶ A} {q' : P' ⟶ B}
    (h : IsPullback p q f g) (h' : IsPullback p' q' f g) (hq : etale q) : etale q' := by
  have e : (h'.isoIsPullback _ _ h).hom ≫ q = q' := h'.isoIsPullback_hom_snd _ _ h
  rw [← e]
  exact (MorphismProperty.cancel_left_of_respectsIso (etale (K := K)) _ q).2 hq

/-- Étale base change along glued fibre products follows from the existence of pullbacks
with étale second projection along étale morphisms of the localized category, together with
the pullback property of the glued fibre product. -/
theorem etaleBaseChange_of_localizedEtalePullback
    (hpull : FibreProductPullbackStatement.{u})
    (hetale : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, u} K) :
    EtaleBaseChangeStatement.{u} := by
  intro K _ _ _ X Y S _ _ _ f g hf
  obtain ⟨P, p, q, hP, hq⟩ :=
    hetale K (localizationFunctor.map f) (localizationFunctor.map g) hf
  exact etale_snd_of_isPullback hP (hpull K X Y S f g) hq

set_option linter.defProp false in
/-- Étale base change along glued fibre products, conditional on effective finite Banach
affinoid algebra descent and on the pullback property of the glued fibre product. It is
declared with `def` (its type is a proposition) so that it can be recorded as a supporting
definition artifact. -/
def etaleBaseChange_of_descent
    (hdesc : PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement.{u})
    (hpull : FibreProductPullbackStatement.{u}) :
    EtaleBaseChangeStatement.{u} :=
  etaleBaseChange_of_localizedEtalePullback hpull fun _ _ _ _ =>
    localizedEtalePullback_of_targetLocality_and_finitePieces
      (AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent hdesc)
      AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces

end Langlands.Analytic.SaturatedAtlasPresentation
