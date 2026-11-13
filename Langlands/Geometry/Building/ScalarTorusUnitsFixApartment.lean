import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.IntegerCentralizer

/-! # Scalar torus units fix the ambient apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {iT : T.toGrp ⟶ G} [Mono iT.hom.hom.left]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (D : KPApartmentData iT (IntegerValuation.order v)) (C : CentralizerDatum iT)

/-- Full V6 fixes the apartment chart under all mapped scalar torus units. -/
def ScalarTorusUnitsFixApartmentStatement : Prop :=
  ∀ (_hD : IntegerValuation.IsOmegaCompatible v D C)
    (f : S ⟶ T) (t : rationalPoints S.toGrp),
    t ∈ characterValuationKernel v S.toGrp →
    ∀ x : D.Apartment,
      rationalPoints.map (CommGroupScheme.groupHom f ≫ iT) t • D.apartmentMap x =
        D.apartmentMap x

/-- Under full V6, the unit kernel of any source mapping into the apartment torus
fixes each apartment point in the original quotient. -/
theorem map_torusUnits_smul_apartmentMap
    (hD : IntegerValuation.IsOmegaCompatible v D C)
    (f : S ⟶ T) (t : rationalPoints S.toGrp)
    (ht : t ∈ characterValuationKernel v S.toGrp) (x : D.Apartment) :
    rationalPoints.map (CommGroupScheme.groupHom f ≫ iT) t • D.apartmentMap x =
      D.apartmentMap x := by
  have hz := IntegerValuation.map_mem_characterValuationKernel v
    (CommGroupScheme.groupHom f ≫ C.s) ht
  have hfix := hD.map_mem_reducedFixer hz x
  rw [D.mem_reducedFixer] at hfix
  change rationalPoints.map ((CommGroupScheme.groupHom f ≫ C.s) ≫ C.j) t •
    D.apartmentMap x = D.apartmentMap x at hfix
  rw [Category.assoc, C.comp_eq] at hfix
  exact hfix

/-- The scalar torus unit statement follows from the full V6 centralizer adapter. -/
theorem scalarTorusUnitsFixApartment :
    ScalarTorusUnitsFixApartmentStatement (S := S) v D C := by
  intro hD f t ht x
  exact D.map_torusUnits_smul_apartmentMap v C hD f t ht x

end KPApartmentData

end Langlands.Geometry.Building
