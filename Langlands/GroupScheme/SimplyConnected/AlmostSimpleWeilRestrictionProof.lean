import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionStatement
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleCompatibleWeilDescent
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.AffineWeilEmbeddingGalois
import Mathlib.FieldTheory.IsSepClosed

/-! # Simply connected almost-simple groups are actual Weil restrictions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme
open Langlands.Algebra.SeparableTensor

namespace SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsSepClosed L]

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

/-- A product decomposition over a separable closure yields all actual Weil witnesses. -/
theorem exists_weilRestriction_of_isSepClosed (hG : IsAlmostSimple G) (i : D.Index) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E)
      (_ : FiniteDimensional k E) (_ : Algebra.IsSeparable k E)
      (H : GroupScheme (Spec (CommRingCat.of E)))
      (_ : IsAffine H.X.left) (_ : LocallyOfFiniteType H.X.hom),
      IsSimplyConnected H ∧ IsAbsolutelyAlmostSimple H ∧
        Nonempty (G ≅ AffineWeil.groupScheme k E H) := by
  have hs : ∀ x : (D.factorStabilizerField i), ((minpoly k x).map (algebraMap k L)).Splits :=
    fun x => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable k x)
  let hb := embeddingEvaluationStatement k (D.factorStabilizerField i) L hs
  have hp := AffineWeil.embeddingProductIsoOfBijective_descent k
    (D.factorStabilizerField i) L hb (D.factorStabilizerDescent i).1
  refine D.exists_weilRestriction_of_compatibleEmbeddingProduct hG i
    (AffineWeil.embeddingProductIsoOfBijective k (D.factorStabilizerField i) L hb
      (D.factorStabilizerDescent i).1) ?_
  intro σ
  set_option backward.isDefEq.respectTransparency true in
    with_reducible exact hp σ

end SimplyConnectedAlmostSimpleProduct

/-- The simply connected refinement of Borel–Tits 6.21(ii), over arbitrary fields. -/
theorem simplyConnectedAlmostSimpleWeilRestriction :
    SimplyConnectedAlmostSimpleWeilRestrictionStatement.{u} := by
  intro k _ G _ hsc hG
  let L := SeparableClosure k
  have hscL := isSimplyConnectedFieldExtension k L G hsc
  let : Smooth G.X.hom := hsc.isSemisimple.isConnectedReductive.smooth
  let : QuasiCompact G.X.hom := inferInstance
  let : QuasiSeparated G.X.hom := inferInstance
  let : LocallyOfFinitePresentation G.X.hom := inferInstance
  let : Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom :=
    hscL.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom :=
    hscL.isSemisimple.isConnectedReductive.isAffineHom
  let D := hscL.almostSimpleProduct
  obtain ⟨i⟩ := D.nonempty_index_of_almostSimple hG
  exact D.exists_weilRestriction_of_isSepClosed hG i

end Langlands.GroupScheme
