import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineChart
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections

/-! # Actual affine sections of relative differentials -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

open Langlands.Scheme.Modules

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ f ⁻¹ᵁ U)

/-- Actual sections of the differential sheaf on an affine chart are canonically
the algebraic Kähler differentials of its actual section rings. -/
def relativeDifferentialsSectionsIso :
    letI := (f.appLE U V h).hom.toAlgebra
    ModuleCat.of Γ(X, V) Γ(relativeDifferentials f, V) ≅
      ModuleCat.of Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V)) := by
  letI := (f.appLE U V h).hom.toAlgebra
  letI : IsIso (fromSpecSectionsLinear (relativeDifferentials f) hV) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (fromSpecSectionsLinear_bijective _ hV)
  letI := relativeDifferentialsSpecMapIsIso Γ(S, U) Γ(X, V)
  exact asIso (fromSpecSectionsLinear (relativeDifferentials f) hV) ≪≫
    (moduleSpecΓFunctor (R := Γ(X, V))).mapIso
      (asIso (relativeDifferentialsAffineChartSquareMap f hU hV h)) ≪≫
    (moduleSpecΓFunctor (R := Γ(X, V))).mapIso
      (asIso (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V))).symm ≪≫
    (tilde.isoTop (ModuleCat.of Γ(X, V)
      (KaehlerDifferential Γ(S, U) Γ(X, V)))).symm

/-- The actual section comparison is characterized by its two canonical
comparisons to the affine Spec differential sheaf. -/
theorem relativeDifferentialsSectionsIso_fac :
    let := (f.appLE U V h).hom.toAlgebra
    (relativeDifferentialsSectionsIso f hU hV h).hom ≫
        (tilde.isoTop (ModuleCat.of Γ(X, V)
          (KaehlerDifferential Γ(S, U) Γ(X, V)))).hom ≫
        (moduleSpecΓFunctor (R := Γ(X, V))).map
          (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V)) =
      fromSpecSectionsLinear (relativeDifferentials f) hV ≫
        (moduleSpecΓFunctor (R := Γ(X, V))).map
          (relativeDifferentialsAffineChartSquareMap f hU hV h) := by
  let := (f.appLE U V h).hom.toAlgebra
  let : IsIso (fromSpecSectionsLinear (relativeDifferentials f) hV) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (fromSpecSectionsLinear_bijective _ hV)
  let := relativeDifferentialsSpecMapIsIso Γ(S, U) Γ(X, V)
  simp only [relativeDifferentialsSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    asIso_hom, asIso_inv, IsIso.inv_hom_id, Category.comp_id]

end Langlands.Scheme
