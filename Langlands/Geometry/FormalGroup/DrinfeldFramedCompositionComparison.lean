import Langlands.Geometry.FormalGroup.DrinfeldFramedCompositionRho

/-! # Original framed comparison for composition of Nilp-base extension -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O T]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X Y : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- When all original transition series are identity, so is actual coefficient composition. -/
theorem baseAlongCompIso_hom_coordinates_of_transition_id (X : BasicAtlas O R σ)
    (ht : ∀ (C : CommAlgCat.{v} R) (a b : X.opens)
      (ha : IsUnit (algebraMap R C a.val)) (hb : IsUnit (algebraMap R C b.val)),
      (X.transition C a b ha hb).hom.toHom.toCoordinateMap = CoordinateMap.id)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (C : CommAlgCat.{v} T)
    (b : (X.baseChangeAlong (g.comp f)).opens) (hb : IsUnit (algebraMap T C b.val)) :
    ((X.baseAlongCompIso f g).hom.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id :=
  (X.baseCompReAlgebraIso_hom_coordinates (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g) C b hb).trans (ht _ _ _ _ _)

namespace OrderAction

variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

/-- Supplied coefficient extension preserves complete identity series of actual integral atlas maps. -/
theorem Iso.baseChangeAlong_hom_coordinates_id (a : Iso E E' h)
    (ha : ∀ (C : CommAlgCat.{v} R) (b : Y.opens)
      (hb : IsUnit (algebraMap R C b.val)),
      (a.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id)
    (m : R →ₐ[O] S) (C : CommAlgCat.{v} S) (b : (Y.baseChangeAlong m).opens)
    (hb : IsUnit (algebraMap S C b.val)) :
    ((a.baseChangeAlong m).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  rw [Iso.baseChangeAlong_hom, Hom.baseChangeAlong_val, BasicAtlas.Hom.baseChangeAlong_coordinates]
  exact ha _ _ _

/-- Equality transport of actual coefficient maps has complete identity chart series. -/
theorem baseAlongEqIso_hom_coordinates (E : OrderAction D X) {m n : R →ₐ[O] S}
    (e : m = n) (C : CommAlgCat.{v} S) (b : (X.baseChangeAlong n).opens)
    (hb : IsUnit (algebraMap S C b.val)) :
    ((E.baseAlongEqIso e).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  cases e
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- A forced composite coefficient correction preserves full identity series when original transitions do. -/
theorem compositionAlongIso_hom_coordinates_of_transition_id (E : OrderAction D X)
    (ht : ∀ (C : CommAlgCat.{v} R) (a b : X.opens)
      (ha : IsUnit (algebraMap R C a.val)) (hb : IsUnit (algebraMap R C b.val)),
      (X.transition C a b ha hb).hom.toHom.toCoordinateMap = CoordinateMap.id)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) {m : R →ₐ[O] T} (hm : m = g.comp f)
    (C : CommAlgCat.{v} T) (b : (X.baseChangeAlong m).opens)
    (hb : IsUnit (algebraMap T C b.val)) :
    ((E.compositionAlongIso f g hm).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  unfold compositionAlongIso
  apply Iso.trans_chart_hom_coordinates_id
  · rw [baseAlongCompIso_hom_val]
    exact X.baseAlongCompIso_hom_coordinates_of_transition_id ht f g C
      (sourceChart (X.baseAlongEqOpens_eq hm.symm) b) hb
  · exact baseAlongEqIso_hom_coordinates E hm.symm C b hb

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S] [Algebra 𝒪[K] T]

/-- The specified original coefficient-composition comparison is induced by its actual atlas isomorphism. -/
theorem baseAlongCompComparison_inducedBy (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    (X.baseAlongCompComparison f g).InducedBy (X.baseAlongCompIso f g) :=
  BasicAtlas.OrderAction.Comparison.inducedBy_ofIso (X.baseAlongCompIso f g)
    (BasicAtlas.CoverRefinement.refl _)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B C : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The specified source map for composite Nilp-base extension has complete identity formal series. -/
theorem baseChangeCompositionSourceIso_hom_coordinates (X : DrinfeldFramedAtlas Φ A)
    (f : A ⟶ B) (g : B ⟶ C)
    (T : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj C).obj)
    (b : (X.baseChange (f ≫ g)).source.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj C).obj T b.val)) :
    ((X.baseChangeCompositionSourceIso f g).hom.val.hom T b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  unfold baseChangeCompositionSourceIso
  apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
  · apply BasicAtlas.OrderAction.Iso.symm_hom_coordinates_id
    exact SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates Φ.val (X.baseChange f).residueMap
      (X.baseChange f).target.val g
  · apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
    · apply BasicAtlas.OrderAction.Iso.symm_hom_coordinates_id
      intro T' b' hb'
      exact BasicAtlas.OrderAction.Iso.baseChangeAlong_hom_coordinates_id _
        (SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates Φ.val X.residueMap X.target.val f)
        (Nilp.reducedScalarMap 𝒪[K] g) T' b' hb'
    · apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
      · apply BasicAtlas.OrderAction.compositionAlongIso_hom_coordinates_of_transition_id
        intro T' a' b' ha' hb'
        exact BasicAtlas.globalTransition_hom_coordinates _ T' a'.val b'.val ha' hb'
      · exact SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original framed comparison between successive and composite actual Nilp-base extensions. -/
def baseChangeCompositionComparison (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    Comparison ((X.baseChange f).baseChange g) (X.baseChange (f ≫ g)) where
  targetComparison := X.target.val.baseAlongCompComparison (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g)
  residue_eq := X.baseChange_comp_residueMap f g
  square := ReducedFramingSquare.of_induced_global_square (X.baseChange_comp_residueMap f g)
    (SpecialAtlas.reductionComparison
      (X.target.val.baseAlongCompComparison (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g)))
    (X.baseChangeCompositionReducedTargetIso f g) (X.baseChangeCompositionSourceIso f g)
    (SpecialAtlas.inducedBy_reduction
      (X.target.val.baseAlongCompComparison (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g))
      (X.target.val.baseAlongCompIso (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g))
      (X.target.val.baseAlongCompComparison_inducedBy (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g)))
    (X.baseChangeCompositionSourceIso_hom_coordinates f g) (X.baseChangeComposition_rho f g)

/-- The original coefficient-composition target comparison is retained exactly. -/
@[simp]
theorem baseChangeCompositionComparison_targetComparison (X : DrinfeldFramedAtlas Φ A)
    (f : A ⟶ B) (g : B ⟶ C) :
    (X.baseChangeCompositionComparison f g).targetComparison =
      X.target.val.baseAlongCompComparison (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g) := rfl

/-- The actual original framed comparison gives composition on representative comparison classes. -/
theorem comparisonClassOf_baseChange_comp (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    comparisonClassOf ((X.baseChange f).baseChange g) = comparisonClassOf (X.baseChange (f ≫ g)) :=
  comparisonClassOf_eq_of_comparison (X.baseChangeCompositionComparison f g)

namespace ComparisonClass

/-- Actual Nilp-base extensions compose on the same original framed chain quotient. -/
theorem baseChange_comp (q : ComparisonClass Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    (q.baseChange f).baseChange g = q.baseChange (f ≫ g) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact comparisonClassOf_baseChange_comp X f g

end ComparisonClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
