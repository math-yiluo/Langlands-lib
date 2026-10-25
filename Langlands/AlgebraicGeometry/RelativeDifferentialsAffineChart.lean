import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineChartMaps
import Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionProof
import Langlands.AlgebraicGeometry.RelativeDifferentialsSpecMapIsIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Affine-chart assembly for relative differentials

The canonical locality and spectrum comparisons give an isomorphism from the
actual restricted differential sheaf to its algebraic model, and transport bases.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (e : V ≤ f ⁻¹ᵁ U)

/-- Open-immersion locality applies to the canonical affine-chart square. -/
instance relativeDifferentialsAffineChartSquareMap_isIso :
    IsIso (relativeDifferentialsAffineChartSquareMap f hU hV e) :=
  relativeDifferentialsOpenImmersionIsIso _ _ _ _ f _ hV.fromSpec hU.fromSpec
    inferInstance inferInstance (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm

/-- The algebraic model comparison is the pullback of the invertible Spec comparison. -/
instance relativeDifferentialsAffineChartFromModelMap_isIso :
    IsIso (relativeDifferentialsAffineChartFromModelMap f hV e) := by
  let := (f.appLE U V e).hom.toAlgebra
  let := relativeDifferentialsSpecMapIsIso Γ(S, U) Γ(X, V)
  change IsIso ((pullback hV.isoSpec.hom).map
    (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V)))
  infer_instance

/-- The canonical affine-chart comparison for the actual relative differential sheaf. -/
def relativeDifferentialsAffineChartIso :
    (relativeDifferentials f).restrict V.ι ≅
      relativeDifferentialsAffineChartModel f hV e :=
  relativeDifferentialsAffineChartPullbackIso f hV ≪≫
    (pullback hV.isoSpec.hom).mapIso
      (asIso (relativeDifferentialsAffineChartSquareMap f hU hV e)) ≪≫
    (asIso (relativeDifferentialsAffineChartFromModelMap f hV e)).symm

/-- The assembled map commutes with the two canonical comparisons. -/
lemma relativeDifferentialsAffineChartIso_fac :
    (relativeDifferentialsAffineChartIso f hU hV e).hom ≫
        relativeDifferentialsAffineChartFromModelMap f hV e =
      relativeDifferentialsAffineChartToSpecMap f hU hV e := by
  simp [relativeDifferentialsAffineChartIso, relativeDifferentialsAffineChartToSpecMap]

/-- Inverse compatibility with the two canonical comparison maps. -/
lemma relativeDifferentialsAffineChartIso_inv_fac :
    (relativeDifferentialsAffineChartIso f hU hV e).inv ≫
        relativeDifferentialsAffineChartToSpecMap f hU hV e =
      relativeDifferentialsAffineChartFromModelMap f hV e := by
  rw [← relativeDifferentialsAffineChartIso_fac f hU hV e]
  simp

/-- The comparison factorization uniquely determines the forward chart morphism. -/
lemma relativeDifferentialsAffineChartIso_hom_unique
    (α : (relativeDifferentials f).restrict V.ι ⟶
      relativeDifferentialsAffineChartModel f hV e)
    (h : α ≫ relativeDifferentialsAffineChartFromModelMap f hV e =
      relativeDifferentialsAffineChartToSpecMap f hU hV e) :
    α = (relativeDifferentialsAffineChartIso f hU hV e).hom := by
  apply (cancel_mono (relativeDifferentialsAffineChartFromModelMap f hV e)).1
  exact h.trans (relativeDifferentialsAffineChartIso_fac f hU hV e).symm

/-- An algebraic chart basis trivializes the actual restricted differential sheaf. -/
def relativeDifferentialsAffineChartBasisIso
    (ι : Type u)
    (b : letI := (f.appLE U V e).hom.toAlgebra
      Module.Basis ι Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))) :
    (relativeDifferentials f).restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) ι :=
  relativeDifferentialsAffineChartIso f hU hV e ≪≫
    relativeDifferentialsAffineChartModelBasisIso f hV e ι b

/-- Actual generating sections obtained by transporting an algebraic chart basis. -/
def relativeDifferentialsAffineChartBasisSections
    (ι : Type u)
    (b : letI := (f.appLE U V e).hom.toAlgebra
      Module.Basis ι Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))) :
    ((relativeDifferentials f).restrict V.ι).GeneratingSections :=
  (SheafOfModules.free.generatingSections ι).ofEpi
    (relativeDifferentialsAffineChartBasisIso f hU hV e ι b).inv

instance relativeDifferentialsAffineChartBasisSections_isIso
    (ι : Type u)
    (b : letI := (f.appLE U V e).hom.toAlgebra
      Module.Basis ι Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))) :
    IsIso (relativeDifferentialsAffineChartBasisSections f hU hV e ι b).π := by
  simp only [relativeDifferentialsAffineChartBasisSections,
    SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  infer_instance

instance relativeDifferentialsAffineChartBasisSections_finite
    (ι : Type u) [Finite ι]
    (b : letI := (f.appLE U V e).hom.toAlgebra
      Module.Basis ι Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))) :
    (relativeDifferentialsAffineChartBasisSections f hU hV e ι b).IsFiniteType where
  finite := inferInstanceAs (Finite ι)

end Langlands.Scheme
