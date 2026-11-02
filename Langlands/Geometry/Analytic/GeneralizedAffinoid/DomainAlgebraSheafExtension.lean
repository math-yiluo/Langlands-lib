import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartAlgebraSheaf

/-! # Finite rational descent extends the actual algebra sheaf to all domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Opposite

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

/-- Extend the actual rational quotient-algebra sheaf by finite rational
multiequalizers. No identification with the stored full-domain algebra is
assumed in this definition. -/
def algebraSheafExtension : Sheaf (finiteDomainTopology K A) (CommAlgCat K) :=
  Functor.OneHypercoverDenseData.essSurj.sheaf
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A)

/-- Restricting the extension to actual rational quotients recovers their
original algebra sheaf, including its actual restriction maps. -/
def rationalAlgebraSheafIso :
    (RationalChart.domainSheafRestriction K A (CommAlgCat K)).obj
        (algebraSheafExtension K A) ≅ RationalChart.algebraSheaf K A :=
  Functor.OneHypercoverDenseData.essSurj.sheafIso
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A)

/-- The section algebra is literally the multiequalizer of the finite chosen
rational quotient family and its actual pairwise intersections. -/
theorem algebraSheafExtension_obj (U : Domain K A) :
    (algebraSheafExtension K A).obj.obj (op U) =
      multiequalizer ((RationalChart.finiteDomainHypercoverData U).multicospanIndex
        (RationalChart.algebraSheaf K A).obj) := rfl

/-- The projection to the actual quotient of a chosen rational cover member. -/
def sectionProjection (U : Domain K A) (i : Fin (finiteRationalCoverData U).size) :
    (algebraSheafExtension K A).obj.obj (op U) ⟶
      CommAlgCat.of K ((finiteRationalCoverData U).chart i).algebra :=
  Functor.OneHypercoverDenseData.essSurj.presheafObjπ
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A) U i

variable {K A}

/-- Agreement after all finite rational projections determines an algebra map. -/
theorem section_hom_ext {U : Domain K A} {Z : CommAlgCat K}
    {f g : Z ⟶ (algebraSheafExtension K A).obj.obj (op U)}
    (h : ∀ i, f ≫ sectionProjection K A U i = g ≫ sectionProjection K A U i) :
    f = g :=
  Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ext h

/-- The finite projections agree after the actual bounded restrictions to
the product-radius rational intersection. -/
theorem sectionProjection_condition (U : Domain K A)
    (i j : Fin (finiteRationalCoverData U).size) :
    sectionProjection K A U i ≫
        CommAlgCat.ofHom (RationalChart.interLeft
          ((finiteRationalCoverData U).chart i)
          ((finiteRationalCoverData U).chart j)).restriction.toAlgHom =
      sectionProjection K A U j ≫
        CommAlgCat.ofHom (RationalChart.interRight
          ((finiteRationalCoverData U).chart i)
          ((finiteRationalCoverData U).chart j)).restriction.toAlgHom :=
  Functor.OneHypercoverDenseData.essSurj.presheafObj_condition
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A) U i j PUnit.unit

variable (K A)

/-- On each rational image object the extension has the original quotient
algebra, through the constructed descent isomorphism. -/
def rationalSectionIso (d : RationalChart K A) :
    (algebraSheafExtension K A).obj.obj (op d.toDomain) ≅ CommAlgCat.of K d.algebra :=
  Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A) d

/-- The chosen rational projections are restriction to their full-domain
images followed by the actual rational section comparison. -/
theorem restrict_rationalSectionIso (U : Domain K A)
    (i : Fin (finiteRationalCoverData U).size) :
    (algebraSheafExtension K A).obj.map ((finiteRationalCoverData U).map i).op ≫
        (rationalSectionIso K A ((finiteRationalCoverData U).chart i)).hom =
      sectionProjection K A U i :=
  Functor.OneHypercoverDenseData.essSurj.presheafMap_presheafObjObjIso_hom
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A) U i

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
