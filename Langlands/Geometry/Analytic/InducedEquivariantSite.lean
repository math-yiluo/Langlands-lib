import Langlands.Geometry.Analytic.InducedSpaceContinuityStatement
import Langlands.Geometry.Analytic.InducedQuasiEtaleStatement
import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite

/-! # Induction on `G`-spaces and on equivariant quasi-étale sites -/

noncomputable section

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})

/-- Induction `X ↦ X_{G/H}` from `H`-spaces to `G`-spaces, for an open subgroup `H`, given the
continuity statement for induced spaces. -/
def gSpaceInduction :
    GSpace.{u, max z v, max z v} K H ⥤ GSpace.{u, max z v, max z v} K G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ inductionFunctor H) fun X =>
    hC K G H hH X.obj X.property

@[simp]
theorem gSpaceInduction_obj_obj (X : GSpace.{u, max z v, max z v} K H) :
    ((gSpaceInduction hH hC).obj X).obj = inducedAction H X.obj := rfl

variable (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H)

/-- Induction on equivariant quasi-étale sites: `U(H) → X(H)` goes to
`U_{G/H}(G) → X_{G/H}(G)`, given the continuity statement and the statement that induction
preserves quasi-étale morphisms. -/
def quasiEtaleSiteInduction :
    EquivariantQuasiEtaleSite X ⥤ EquivariantQuasiEtaleSite ((gSpaceInduction hH hC).obj X) :=
  MorphismProperty.Comma.lift
    (MorphismProperty.Over.forget _ _ X ⋙ Over.post (gSpaceInduction hH hC))
    (fun U => (hQ K G H ((ObjectProperty.ι _).map U.hom)).1 U.prop)
    (fun _ => trivial) (fun _ => trivial)

@[simp]
theorem quasiEtaleSiteInduction_obj_left (U : EquivariantQuasiEtaleSite X) :
    ((quasiEtaleSiteInduction hH hC hQ X).obj U).left = (gSpaceInduction hH hC).obj U.left :=
  rfl

@[simp]
theorem quasiEtaleSiteInduction_map_left {U V : EquivariantQuasiEtaleSite X} (f : U ⟶ V) :
    ((quasiEtaleSiteInduction hH hC hQ X).map f).left = (gSpaceInduction hH hC).map f.left :=
  rfl

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
