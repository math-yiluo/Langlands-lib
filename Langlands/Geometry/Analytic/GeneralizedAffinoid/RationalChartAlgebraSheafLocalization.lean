import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartAlgebraSheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartRelativeComparison
import Mathlib.CategoryTheory.Sites.Over

/-! # Localization of the finite rational algebra sheaf over a chart -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- A chart over `d` gives its actual coefficient pullback over `d.algebra`. -/
def relativeChartFunctor (d : RationalChart K A) :
    Over d ⥤ RationalChart K d.algebra :=
  Over.forget d ⋙ pullbackFunctor d.baseMap

/-- Continuity uses the slice topology and the proved continuity of bounded
coefficient change on the finite rational sites. -/
instance relativeChartFunctor_isContinuous (d : RationalChart K A) :
    Functor.IsContinuous (relativeChartFunctor d)
      ((finiteRationalTopology K A).over d) (finiteRationalTopology K d.algebra) :=
  Functor.isContinuous_comp (Over.forget d) (pullbackFunctor d.baseMap)
    ((finiteRationalTopology K A).over d) (finiteRationalTopology K A)
    (finiteRationalTopology K d.algebra)

/-- The actual algebra sheaf over `d.algebra`, viewed on the slice over `d`
by the constructed continuous relative-chart functor. -/
def relativeAlgebraSheaf (d : RationalChart K A) :
    Sheaf ((finiteRationalTopology K A).over d) (CommAlgCat K) :=
  ((relativeChartFunctor d).sheafPushforwardContinuous (CommAlgCat K)
    ((finiteRationalTopology K A).over d)
    (finiteRationalTopology K d.algebra)).obj (algebraSheaf K d.algebra)

@[simp]
theorem relativeAlgebraSheaf_obj (d : RationalChart K A) (U : Over d) :
    (relativeAlgebraSheaf d).obj.obj (Opposite.op U) =
      CommAlgCat.of K (pullback d.baseMap U.left).algebra := rfl

@[simp]
theorem relativeAlgebraSheaf_map_apply {d : RationalChart K A}
    {U V : Over d} (f : U ⟶ V) (a : (pullback d.baseMap V.left).algebra) :
    (relativeAlgebraSheaf d).obj.map f.op a =
      (pullbackRestriction d.baseMap f.left).restriction a := rfl

/-- Restricting the ambient algebra sheaf to the slice over `d` agrees with
the actual algebra sheaf over `d.algebra` along `relativeChartFunctor`.
The components are the previously constructed bounded relative equivalences. -/
def relativeAlgebraSheafIso (d : RationalChart K A) :
    (algebraSheaf K A).over d ≅ relativeAlgebraSheaf d :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => CommAlgCat.isoMk U.unop.hom.relativeEquiv.toAlgEquiv)
    (by
      intro U V f
      ext a
      exact congrArg
        (fun g : BoundedAlgHom K U.unop.left.algebra
          (pullback d.baseMap V.unop.left).algebra => g a)
        (pullbackRestriction_comp_pullbackMap d.baseMap f.unop.left).symm))

@[simp]
theorem relativeAlgebraSheafIso_hom_apply (d : RationalChart K A)
    (U : Over d) (a : U.left.algebra) :
    (relativeAlgebraSheafIso d).hom.hom.app (Opposite.op U) a =
      pullbackMap d.baseMap U.left a := rfl

@[simp]
theorem relativeAlgebraSheafIso_inv_apply (d : RationalChart K A)
    (U : Over d) (a : (pullback d.baseMap U.left).algebra) :
    (relativeAlgebraSheafIso d).inv.hom.app (Opposite.op U) a =
      U.hom.relativeInverse a := rfl

/-- The forward comparison carries the original restriction from `d`
to the structural map of the pulled-back quotient. -/
@[simp]
theorem relativeAlgebraSheafIso_hom_restriction (d : RationalChart K A)
    (U : Over d) (a : d.algebra) :
    (relativeAlgebraSheafIso d).hom.hom.app (Opposite.op U)
        (U.hom.restriction a) =
      (pullback d.baseMap U.left).baseMap a :=
  congrArg (fun g : BoundedAlgHom K d.algebra
    (pullback d.baseMap U.left).algebra => g a) U.hom.pullbackMap_comp_restriction

/-- The inverse comparison carries the localized structural map back to
the actual restriction from `d`. -/
@[simp]
theorem relativeAlgebraSheafIso_inv_baseMap (d : RationalChart K A)
    (U : Over d) (a : d.algebra) :
    (relativeAlgebraSheafIso d).inv.hom.app (Opposite.op U)
        ((pullback d.baseMap U.left).baseMap a) =
      U.hom.restriction a :=
  congrArg (fun g : BoundedAlgHom K d.algebra U.left.algebra => g a)
    U.hom.relativeInverse_comp_baseMap

/-- The comparison is precisely the restriction of the existing coefficient
sheaf morphism along `d.baseMap` to the slice, at every chart. -/
theorem relativeAlgebraSheafIso_hom_coefficientMap (d : RationalChart K A)
    (U : Over d) :
    (relativeAlgebraSheafIso d).hom.hom.app (Opposite.op U) =
      (algebraSheafMap d.baseMap).hom.app (Opposite.op U.left) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
