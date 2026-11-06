import Langlands.Geometry.Analytic.FullRecognitionNaturality
import Langlands.Geometry.Analytic.RecognizedLocalDomainCategory

/-! # Full-recognition idempotence as an equivalence of affinoid diagrams -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Recognize the actual whole local-domain presentation of an earlier
full-recognition chart inside the iterated full atlas. -/
def fullRecognitionIterationIndex (V : a.saturatedAtlas.RecognizedSubset) :
    a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset :=
  a.fullRecognitionAtlas.recognizedLocalDomain
    (a.fullRecognitionAtlas.originalLocalDomain V)

@[simp]
theorem fullRecognitionIterationIndex_locus (V : a.saturatedAtlas.RecognizedSubset) :
    (a.fullRecognitionIterationIndex V).locus = V.locus :=
  (a.fullRecognitionAtlas.recognizedLocalDomain_locus _).trans
    ((a.fullRecognitionAtlas.originalLocalDomain_locus V).trans V.range_chart)

/-- Every earlier recognized inclusion gives an iterated recognized
inclusion through the same literal ambient subsets. -/
def fullRecognitionIterationFunctor :
    a.saturatedAtlas.RecognizedSubset ⥤
      a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset where
  obj := a.fullRecognitionIterationIndex
  map {U V} f := ⟨by
    rw [a.fullRecognitionIterationIndex_locus, a.fullRecognitionIterationIndex_locus]
    exact f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The iterated round trip is isomorphic to the identity by literal
inclusions in both directions on the unchanged locus. -/
def fullRecognitionIdempotenceUnitComponent
    (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset) :
    W ≅ a.fullRecognitionIterationFunctor.obj
      (a.fullRecognitionIdempotenceFunctor.obj W) where
  hom := ⟨(a.fullRecognitionIterationIndex_locus
    (a.fullRecognitionIdempotenceIndex W)).symm.subset⟩
  inv := ⟨(a.fullRecognitionIterationIndex_locus
    (a.fullRecognitionIdempotenceIndex W)).subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def fullRecognitionIdempotenceUnitIso :
    𝟭 a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset ≅
      a.fullRecognitionIdempotenceFunctor ⋙ a.fullRecognitionIterationFunctor :=
  NatIso.ofComponents (a.fullRecognitionIdempotenceUnitComponent) (by
    intro U V f
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- The earlier round trip is isomorphic to the identity on the same
literal subsets; all inverse identities use inclusion uniqueness. -/
def fullRecognitionIdempotenceCounitComponent (V : a.saturatedAtlas.RecognizedSubset) :
    a.fullRecognitionIdempotenceFunctor.obj
      (a.fullRecognitionIterationFunctor.obj V) ≅ V where
  hom := ⟨(a.fullRecognitionIterationIndex_locus V).subset⟩
  inv := ⟨(a.fullRecognitionIterationIndex_locus V).symm.subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def fullRecognitionIdempotenceCounitIso :
    a.fullRecognitionIterationFunctor ⋙ a.fullRecognitionIdempotenceFunctor ≅
      𝟭 a.saturatedAtlas.RecognizedSubset :=
  NatIso.ofComponents (a.fullRecognitionIdempotenceCounitComponent) (by
    intro U V f
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- Full recognition is idempotent as an actual equivalence of recognized
inclusion categories, with both functors and round trips constructed. -/
def fullRecognitionIdempotenceEquivalence :
    a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset ≌
      a.saturatedAtlas.RecognizedSubset where
  functor := a.fullRecognitionIdempotenceFunctor
  inverse := a.fullRecognitionIterationFunctor
  unitIso := a.fullRecognitionIdempotenceUnitIso
  counitIso := a.fullRecognitionIdempotenceCounitIso
  functor_unitIso_comp W := @Subsingleton.elim
    (RecognizedSubset.Inclusion (a.fullRecognitionIdempotenceFunctor.obj W)
      (a.fullRecognitionIdempotenceFunctor.obj W)) inferInstance _ _

/-- The bounded idempotence comparison gives mutually inverse actual
affinoid morphisms, retaining the entire algebra maps. -/
def fullRecognitionIdempotenceAffinoidIso
    (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset) :
    Opposite.op (a.fullRecognitionIdempotenceIndex W).algebra ≅
      Opposite.op W.algebra where
  hom := Quiver.Hom.op
    (show W.algebra ⟶ (a.fullRecognitionIdempotenceIndex W).algebra from
      (a.fullRecognitionIdempotenceAlgebraEquiv W).toBoundedAlgHom)
  inv := Quiver.Hom.op
    (show (a.fullRecognitionIdempotenceIndex W).algebra ⟶ W.algebra from
      (a.fullRecognitionIdempotenceAlgebraEquiv W).symm.toBoundedAlgHom)
  hom_inv_id := congrArg
    (fun q : (a.fullRecognitionIdempotenceIndex W).algebra ⟶
      (a.fullRecognitionIdempotenceIndex W).algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x =>
      (a.fullRecognitionIdempotenceAlgebraEquiv W).apply_symm_apply x)
  inv_hom_id := congrArg (fun q : W.algebra ⟶ W.algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x =>
      (a.fullRecognitionIdempotenceAlgebraEquiv W).symm_apply_apply x)

/-- The category equivalence identifies the entire presented-affinoid
diagrams, by the already proved full bounded restriction naturality. -/
def fullRecognitionIdempotenceAffinoidNatIso :
    a.fullRecognitionIdempotenceFunctor ⋙
        RecognizedSubset.toAffinoidSpace a.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace a.fullRecognitionAtlas.saturatedAtlas :=
  NatIso.ofComponents (a.fullRecognitionIdempotenceAffinoidIso) (by
    intro U V f
    exact congrArg
      (fun q : V.algebra ⟶ (a.fullRecognitionIdempotenceIndex U).algebra =>
        Quiver.Hom.op q)
      (a.fullRecognitionIdempotenceFunctor_naturality f).symm)

/-- The natural comparison also identifies the actual spectrum maps over
the fixed ambient space, on every point. -/
theorem fullRecognitionIdempotenceAffinoidNatIso_over_ambient
    (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (a.fullRecognitionIdempotenceIndex W).algebra) :
    W.chart ((affinoidSpectrumFunctor K).map
        (a.fullRecognitionIdempotenceAffinoidNatIso.hom.app W) x) =
      (a.fullRecognitionIdempotenceIndex W).chart x :=
  (a.fullRecognitionIdempotenceIndex_chart W x).symm

end Langlands.Analytic.IndexedAffinoidAtlas
