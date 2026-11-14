import Langlands.Geometry.FormalGroup.AtlasOrderRefinement
import Langlands.Geometry.FormalGroup.SpecialAtlas

/-! # Refinement of special formal division-order atlases -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable (X : SpecialAtlas K D ι R) (q : BasicAtlas.CoverRefinement X.atlas)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restrict actual special chart laws, their order action and tangent certificates. -/
def refine : SpecialAtlas K D ι R where
  atlas := q.atlas
  order := q.orderAction X.order
  unramified := X.unramified
  tangent b := (X.tangent (q.source b)).map (q.chartCoefficient b)

/-- Refinement preserves the actual chart scalar-kernel heights and base nilpotence. -/
theorem refine_height {π : 𝒪[K]} (h : X.HasHeightSquared π) :
    (X.refine q).HasHeightSquared π :=
  ⟨h.1, h.2.1, fun b => (h.2.2 (q.source b)).map (q.chartCoefficient b)⟩

/-- The restricted special chart has its selected original chart's actual order points. -/
def refinementChartEquiv (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (X.refine q).order.ChartPoint A b hb ≃ₗ[IntegerRing K D]
      X.order.ChartPoint A (q.source b) (q.source_unit A b hb) :=
  q.orderChartEquiv X.order A b hb

@[simp]
theorem refinementChartEquiv_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (x : (X.refine q).order.ChartPoint A b hb) :
    X.refinementChartEquiv q A b hb x = x :=
  q.orderChartEquiv_apply X.order A b hb x

@[simp]
theorem refinementChartEquiv_symm_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (x : X.order.ChartPoint A (q.source b) (q.source_unit A b hb)) :
    (X.refinementChartEquiv q A b hb).symm x = x :=
  q.orderChartEquiv_symm_apply X.order A b hb x

/-- Restriction and actual coefficient gluing give a full division-order-linear equivalence. -/
def refinementPointEquiv (A : CommAlgCat.{v} R) :
    X.Point A ≃ₗ[IntegerRing K D] (X.refine q).Point A :=
  q.orderPointEquiv X.order A

@[simp]
theorem refinementPointEquiv_apply (A : CommAlgCat.{v} R) (x : X.Point A)
    (t : q.atlas.ChartTest A) :
    (X.refinementPointEquiv q A x).val t = x.val (q.restrictTest t) := rfl

@[simp]
theorem refinementPointEquiv_symm_apply (A : CommAlgCat.{v} R)
    (y : (X.refine q).Point A) (t : X.atlas.ChartTest A) :
    ((X.refinementPointEquiv q A).symm y).val t = q.gluedValue y t := rfl

/-- Restriction of complete families commutes with every coefficient-algebra map. -/
theorem refinementPointEquiv_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : X.Point A) :
    (X.refine q).order.mapPoints φ (X.refinementPointEquiv q A x) =
      X.refinementPointEquiv q B (X.order.mapPoints φ x) :=
  q.orderOnPoints_natural X.order φ x

/-- The actual special-atlas point functors are naturally isomorphic after refinement. -/
def refinementPointFunctorIso : X.pointFunctor ≅ (X.refine q).pointFunctor :=
  q.orderPointFunctorIso X.order

/-- The same constructed natural isomorphism on coefficient tests where pi is nilpotent. -/
def refinementNilpPointFunctorIso (π : R) :
    X.nilpPointFunctor π ≅ (X.refine q).nilpPointFunctor π :=
  q.orderNilpPointFunctorIso X.order π

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
