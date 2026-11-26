import Langlands.Geometry.Analytic.AffineAnalytificationAtlas
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Finiteness of étale cohomology on compact analytic spaces

Berkovich 1994, Corollary 5.6, in the case of local charts admitting
quasi-étale morphisms to affine analytifications. The coefficients are
finite locally constant module sheaves of order prime to the residue
characteristic.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory Set Filter
open scoped Topology
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology

universe u v uR

/-- At every point there is a neighbourhood given by finitely many affinoid
chart ranges, each with a quasi-étale map to an affine analytification. -/
def HasQuasiAlgebraicAffinoidNeighbourhoods
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, u, u} (K := K)) : Prop :=
  let A := presentationOf X
  ∀ x : A.presentation.space, ∃ charts : Finset A.presentation.atlas.Index,
    (⋃ i ∈ charts, range (A.presentation.atlas.chart i)) ∈ 𝓝 x ∧
    ∀ i ∈ charts,
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra K B) (P : FinitePolynomialPresentation K B)
        (f : localizationFunctor.obj (A.domain (A.chartDomain i)) ⟶
          AffineAnalytification.localized K P), quasiEtale f

/-- A module sheaf is finite locally constant if a jointly surjective family
of étale objects trivializes it by constant sheaves of finite modules. -/
def IsFiniteLocallyConstantAnalyticEtaleSheaf
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {X : LocalizedCategory.{u, v, v} (K := K)}
    (R : Type (max u (v + 1) uR)) [CommRing R]
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uR} R)) : Prop :=
  ∀ x : localizedSpaceFunctor.obj X,
    ∃ (U : EtaleSite X) (M : ModuleCat.{max u (v + 1) uR} R),
      x ∈ range (localizedSpaceFunctor.map U.hom) ∧ Finite M ∧
      haveI := etale_hasSheafify.{u, v, uR} U.left R
      Nonempty ((MorphismProperty.Over.map ⊤ U.prop).op ⋙ F.obj ≅
        ((constantSheaf (etaleTopology U.left) (ModuleCat.{max u (v + 1) uR} R)).obj M).obj)

/-- For the prime-to-residue-characteristic finite locally constant sheaves
on a compact analytic space with quasi-algebraic affinoid neighbourhoods,
all ordinary étale cohomology groups are finite. -/
def AnalyticEtaleFinitenessStatement
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] (X : LocalizedCategory.{u, u, u} (K := K)) : Prop :=
  IsCompactSpace X → HasQuasiAlgebraicAffinoidNeighbourhoods X →
    ∀ N : ℕ, 0 < N → ‖(N : K)‖ = 1 →
      let R := ULift.{max (u + 1) uR} (ZMod N)
      ∀ F : Sheaf (etaleTopology X) (ModuleCat.{max (u + 1) uR} R),
        IsFiniteLocallyConstantAnalyticEtaleSheaf.{u, u, uR} R F →
        ∀ q : ℕ, Finite ((etaleCohomology.{u, u, uR} X R q).obj F)

end Langlands.Cohomology
