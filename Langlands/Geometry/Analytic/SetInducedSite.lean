import Langlands.Geometry.Analytic.SetInducedSpaceContinuityStatement
import Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleStatement
import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite
import Langlands.Topology.GroupAction.DiscreteGSetSite

/-! # Berkovich's functor `Σ ↦ X_Σ(G)` from `P(G)` to `Qét(X(G))` and `Ét(X(G))` -/

noncomputable section

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G]

/-! ## `Σ ↦ X_Σ` on all `G`-sets -/

section Action

variable (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G)

/-- Berkovich's correspondence `Σ ↦ X_Σ` on `G`-sets. -/
@[simps]
def setInducedFunctor :
    Action (Type z) G ⥤ Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G where
  obj S := setInduced X S.V
  map f := map X (Action.gMap f)
  map_id S := by
    rw [Action.gMap_id]
    exact map_id X
  map_comp f g := by
    rw [Action.gMap_comp]
    exact map_comp X _ _

/-- `Σ ↦ (X_Σ → X)`: the spaces `X_Σ` with their projections, over `X`. -/
def overFunctor : Action (Type z) G ⥤ Over X :=
  (setInducedFunctor X).toOver X (fun S => projection X S.V) fun f =>
    map_projection X (Action.gMap f)

@[simp]
theorem overFunctor_obj_hom (S : Action (Type z) G) :
    ((overFunctor X).obj S).hom = projection X S.V := rfl

/-- The projection `X_Σ → X` is quasi-étale and étale, given the statement on morphisms out of
disjoint unions: it is the codiagonal of the disjoint union of copies of `X`. -/
theorem projectionHom_quasiEtale_etale (hD : SigmaDescStatement.{u, v, z}) (S : Type z) :
    quasiEtale (projectionHom X S) ∧ etale (projectionHom X S) :=
  ⟨(hD K S (fun _ => X.V) X.V fun _ => 𝟙 _).1 fun _ => (quasiEtale (K := K)).id_mem _,
    (hD K S (fun _ => X.V) X.V fun _ => 𝟙 _).2 fun _ => (etale (K := K)).id_mem _⟩

end Action

/-! ## Discrete `G`-sets and `G`-spaces -/

variable [TopologicalSpace G] [IsTopologicalGroup G] (hC : ContinuityStatement.{u, v, z})
  (X : GSpace.{u, max z v, max z v} K G)

/-- `Σ ↦ X_Σ` from discrete `G`-sets to `G`-spaces, given the continuity statement. -/
def gSpaceFunctor : DiscreteGSet G ⥤ GSpace.{u, max z v, max z v} K G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ setInducedFunctor X.obj) fun S =>
    hC K G X.obj S.obj.V S.property X.property

@[simp]
theorem gSpaceFunctor_obj_obj (S : DiscreteGSet G) :
    ((gSpaceFunctor hC X).obj S).obj = setInduced X.obj S.obj.V := rfl

/-- `Σ ↦ (X_Σ(G) → X(G))` over `X` in the category of `G`-spaces. -/
def gSpaceOverFunctor : DiscreteGSet G ⥤ Over X :=
  (gSpaceFunctor hC X).toOver X (fun S => ObjectProperty.homMk (projection X.obj S.obj.V))
    fun f => ObjectProperty.hom_ext _ (map_projection X.obj (Action.gMap f.hom))

@[simp]
theorem gSpaceOverFunctor_obj_hom_hom (S : DiscreteGSet G) :
    ((gSpaceOverFunctor hC X).obj S).hom.hom = projection X.obj S.obj.V := rfl

/-! ## Berkovich's `γ` -/

variable (hD : SigmaDescStatement.{u, v, z})

/-- Berkovich's `γ` (1996, §1.2), quasi-étale case: `Σ ↦ X_Σ(G)` from `P(G)` to `Qét(X(G))`,
given the continuity statement for `X_Σ` and the statement on morphisms out of disjoint
unions. -/
def quasiEtaleSiteFunctor : DiscreteGSet G ⥤ EquivariantQuasiEtaleSite X :=
  MorphismProperty.Comma.lift (gSpaceOverFunctor hC X)
    (fun S => (projectionHom_quasiEtale_etale X.obj hD S.obj.V).1)
    (fun _ => trivial) (fun _ => trivial)

@[simp]
theorem quasiEtaleSiteFunctor_obj_left (S : DiscreteGSet G) :
    ((quasiEtaleSiteFunctor hC X hD).obj S).left = (gSpaceFunctor hC X).obj S := rfl

@[simp]
theorem quasiEtaleSiteFunctor_map_left {S T : DiscreteGSet G} (f : S ⟶ T) :
    ((quasiEtaleSiteFunctor hC X hD).map f).left = (gSpaceFunctor hC X).map f := rfl

/-- Berkovich's `γ` (1996, §1.2), étale case: `Σ ↦ X_Σ(G)` from `P(G)` to `Ét(X(G))`. -/
def etaleSiteFunctor : DiscreteGSet G ⥤ EquivariantEtaleSite X :=
  MorphismProperty.Comma.lift (gSpaceOverFunctor hC X)
    (fun S => (projectionHom_quasiEtale_etale X.obj hD S.obj.V).2)
    (fun _ => trivial) (fun _ => trivial)

@[simp]
theorem etaleSiteFunctor_obj_left (S : DiscreteGSet G) :
    ((etaleSiteFunctor hC X hD).obj S).left = (gSpaceFunctor hC X).obj S := rfl

/-- The étale and quasi-étale versions of `γ` agree under `Ét(X(G)) → Qét(X(G))`. -/
theorem etaleSiteFunctor_comp_ofEquivariantEtaleSite :
    etaleSiteFunctor hC X hD ⋙ EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X =
      quasiEtaleSiteFunctor hC X hD :=
  rfl

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
