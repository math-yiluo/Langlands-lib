import Langlands.AlgebraicGeometry.Picard.ParallelIsomorphismPullback
import Langlands.CategoryTheory.OverTotalRepresentable

/-! # Smooth full endpoint-kernel projections for actual Picard arrows -/

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U)) (a b : T ⟶ U)
  {P : Over T.left}
  (eP : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ parallelIsomorphismPresheaf f L a b)

/-- A slice representative of parallel arrows represents the full endpoint
base change after totalization. -/
def totalParallelIsomorphismRepresentation :
    (totalParallelIsomorphismPresheaf f L a b).RepresentableBy
      (T.iteratedSliceBackward.obj P).left := by
  let e₁ := (Functor.RepresentableBy.equivUliftYonedaIso _ P).symm eP
  let e₂ := Functor.representableByUliftFunctorEquiv e₁
  let e₃ := Functor.RepresentableBy.ofEquivalence T.iteratedSliceEquiv.symm e₂
  exact Functor.representableByUliftFunctorEquiv.symm e₃.toOverTotal

/-- The complete parallel-arrow representation as a natural isomorphism. -/
def totalParallelIsomorphismSchemeIso :
    (AlgebraicSpace.schemeYoneda S).obj (T.iteratedSliceBackward.obj P).left ≅
      totalParallelIsomorphismPresheaf f L a b :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _)
    (totalParallelIsomorphismRepresentation f L a b eP)

/-- Totalization retains exactly the slice representative's structure map. -/
lemma totalParallelIsomorphismSchemeIso_base :
    (totalParallelIsomorphismSchemeIso f L a b eP).hom ≫
        totalParallelIsomorphismBaseMap f L a b =
      (AlgebraicSpace.schemeYoneda S).map (T.iteratedSliceBackward.obj P).hom := by
  ext V g
  rfl

/-- At a pair with an actual arrow, the full endpoint base change is an
actual smooth scheme over the common base. -/
lemma exists_smoothEndpointPullback
    (e : ((relative f).map a.op.toLoc).toFunctor.obj (Core.mk L) ≅
      ((relative f).map b.op.toLoc).toFunctor.obj (Core.mk L))
    (h : HasSmoothRelativeAutomorphismSchemes f) :
    ∃ (P : Over S) (p : P ⟶ T)
      (z : (AlgebraicSpace.schemeYoneda S).obj P ⟶ atlasArrowPresheaf f L),
      IsPullback z ((AlgebraicSpace.schemeYoneda S).map p) (atlasArrowEndpoint f L)
        (familyEndpointMap a b) ∧ Smooth p.left := by
  obtain ⟨P, ⟨eP⟩, hP⟩ := exists_parallelIsomorphismScheme f L a b e h
  let E := totalParallelIsomorphismSchemeIso f L a b eP
  refine ⟨(T.iteratedSliceBackward.obj P).left, (T.iteratedSliceBackward.obj P).hom,
    E.hom ≫ totalParallelIsomorphismArrowMap f L a b, ?_, hP⟩
  apply (totalParallelIsomorphism_isPullback f L a b).of_iso'
    E (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa using totalParallelIsomorphismSchemeIso_base f L a b eP
  · simp
  · simp

/-- Every full endpoint-kernel projection is represented and smooth on all
scheme base changes, using the actual arrow on each test as the torsor section. -/
lemma smooth_endpointKernel_projection {K : AlgebraicSpace.Presheaf S}
    {r s : K ⟶ atlasArrowPresheaf f L}
    (hK : IsPullback r s (atlasArrowEndpoint f L) (atlasArrowEndpoint f L))
    (h : HasSmoothRelativeAutomorphismSchemes f) :
    (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).relative
      (AlgebraicSpace.schemeYoneda S) s := by
  let : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    smooth_isStableUnderBaseChange.respectsIso
  let := MorphismProperty.RespectsIso.inverseImage (@Smooth.{u}) (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro T g
  let x := uliftYonedaEquiv g
  let a : T ⟶ U := x.down.2.1
  let b : T ⟶ U := x.down.1
  have hg : familyEndpointMap a b = g ≫ atlasArrowEndpoint f L := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp]
    change ULift.up ((𝟙 T) ≫ a, (𝟙 T) ≫ b) = ULift.up (a, b)
    simp only [Category.id_comp]
  obtain ⟨P, p, z, hP, hp⟩ := exists_smoothEndpointPullback f L a b x.down.2.2 h
  rw [hg] at hP
  exact ⟨P, _, p, hP.of_right' hK, hp⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
