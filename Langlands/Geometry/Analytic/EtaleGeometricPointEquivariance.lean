import Langlands.Geometry.Analytic.EtaleGeometricPoints
import Langlands.Sheaf.Equivariant.TwistedCompactSupport

/-! # Group actions on the field-valued points of an analytic space -/

noncomputable section

universe u v uL uG

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [NormedAlgebra K L]

namespace EtaleSite

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type uG} [Group G] (ρ : G →* Aut X)

/-- A group acting on `X` by automorphisms acts on the `L`-valued points of `X`:
`g • x` is the image of `x` under `ρ g`. -/
abbrev pointAction : MulAction G ((localizedFieldPointFunctor L).obj X) where
  smul g x := (localizedFieldPointFunctor L).map (ρ g).hom x
  one_smul x := by
    change (localizedFieldPointFunctor L).map (ρ 1).hom x = x
    rw [map_one]
    exact (localizedFieldPointFunctor L).map_id_apply X x
  mul_smul g h x := by
    change (localizedFieldPointFunctor L).map (ρ (g * h)).hom x =
      (localizedFieldPointFunctor L).map (ρ g).hom ((localizedFieldPointFunctor L).map (ρ h).hom x)
    rw [map_mul]
    exact (localizedFieldPointFunctor L).map_comp_apply (ρ h).hom (ρ g).hom x

theorem pointAction_smul (g : G) (x : (localizedFieldPointFunctor L).obj X) :
    (pointAction L ρ).toSMul.smul g x = (localizedFieldPointFunctor L).map (ρ g).hom x := rfl

/-- If every `L`-valued point of `X` satisfies the point axioms, the resulting family of points
of the étale site, indexed by the `L`-valued points with the action through `ρ`, is compatible
with the translations of `Ét(X)`: the fibre of `gU` at `g • x` is the fibre of `U` at `x`. -/
def pointEquivariance (h : ∀ x : (localizedFieldPointFunctor L).obj X, PointAxioms L x) :
    letI := pointAction L ρ
    Sheaf.Equivariant.TwistedOver.PointEquivariance (P := etale (K := K))
      (J := etaleTopology X) ρ (fun x => toPoint L x (h x)) :=
  letI := pointAction L ρ
  { fiberIso := fun g x => pointTranslate L (ρ g) x (h x) (h _) }

end EtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
