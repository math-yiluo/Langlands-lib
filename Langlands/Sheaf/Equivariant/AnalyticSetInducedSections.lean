import Langlands.Topology.GroupAction.DiscreteGSetFibre
import Langlands.Geometry.Analytic.SetInducedSite
import Langlands.Geometry.Analytic.EquivariantEtaleSite

/-! # Berkovich's functor `Γ_{X{G}}` from sheaves on `X(G)` to smooth representations -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.DiscreteGSet

universe u v z w uR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (hC : SetInducedSpace.ContinuityStatement.{u, v, z}) (hD : SigmaDescStatement.{u, v, z})
  (X : GSpace.{u, max z v, max z v} K G) (R : Type uR) [CommRing R]

/-! ## The quasi-étale case -/

section QuasiEtale

/-- The presheaf `γ_*F : Σ ↦ F(X_Σ(G))` on `P(G)` of a presheaf `F` of `R`-modules on
`Qét(X(G))`, where `γ : Σ ↦ X_Σ(G)` is Berkovich's functor. -/
def quasiEtaleSetInducedPresheaf :
    ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max z w} R) ⥤
      ((DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{max z w} R) :=
  (Functor.whiskeringLeft _ _ _).obj (SetInducedSpace.quasiEtaleSiteFunctor hC X hD).op

@[simp]
theorem quasiEtaleSetInducedPresheaf_obj_obj
    (F : (EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max z w} R) (S : DiscreteGSet G) :
    ((quasiEtaleSetInducedPresheaf hC hD X R).obj F).obj (op S) =
      F.obj (op ((SetInducedSpace.quasiEtaleSiteFunctor hC X hD).obj S)) :=
  rfl

/-- **Berkovich's `Γ_{X{G}}`**, quasi-étale case (1996, §1.2): a sheaf `F` of `R`-modules on
`X(G)_qét` goes to the fibre of `Σ ↦ F(X_Σ(G))` over the pointed orbits `(G ⧸ N, a)`, a smooth
representation of `G` in which `g` sends the image of `F(X_{G/N}(G))` at `a` to its image at
`g • a`. -/
def quasiEtaleSetInducedSections :
    Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{max z w} R) ⥤
      SmoothRep.{uR, z, max z w} R G :=
  haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
  sheafToPresheaf _ _ ⋙ quasiEtaleSetInducedPresheaf.{u, v, z, w} hC hD X R ⋙
    fibreFunctor G R

theorem quasiEtaleSetInducedSections_obj
    (F : Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{max z w} R)) :
    haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
    (quasiEtaleSetInducedSections.{u, v, z, w} hC hD X R).obj F =
      fibreRep ((quasiEtaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj) :=
  rfl

/-- **Berkovich's formula** `Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G))` (1996, §1.2): the colimit
of the `F(X_{G/N}(G))` over the open subgroups `N` of `G` is the module underlying
`Γ_{X{G}}(F)`. -/
def quasiEtaleSetInducedSectionsIso
    (F : Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{max z w} R)) :
    haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
    colimit ((basePoint G).op ⋙
        fibreDiagram ((quasiEtaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj)) ≅
      fibre ((quasiEtaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj) :=
  haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
  colimitOpenSubgroupIsoFibre _

end QuasiEtale

/-! ## The étale case -/

section Etale

/-- The presheaf `γ_*F : Σ ↦ F(X_Σ(G))` on `P(G)` of a presheaf `F` of `R`-modules on
`Ét(X(G))`. -/
def etaleSetInducedPresheaf :
    ((EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max z w} R) ⥤
      ((DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{max z w} R) :=
  (Functor.whiskeringLeft _ _ _).obj (SetInducedSpace.etaleSiteFunctor hC X hD).op

@[simp]
theorem etaleSetInducedPresheaf_obj_obj
    (F : (EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max z w} R) (S : DiscreteGSet G) :
    ((etaleSetInducedPresheaf hC hD X R).obj F).obj (op S) =
      F.obj (op ((SetInducedSpace.etaleSiteFunctor hC X hD).obj S)) :=
  rfl

/-- **Berkovich's `Γ_{X{G}}`**, étale case (1996, §1.2): a sheaf `F` of `R`-modules on
`X(G)_ét` goes to the fibre of `Σ ↦ F(X_Σ(G))` over the pointed orbits, a smooth
representation of `G`. -/
def etaleSetInducedSections :
    Sheaf (equivariantEtaleTopology X) (ModuleCat.{max z w} R) ⥤
      SmoothRep.{uR, z, max z w} R G :=
  haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
  sheafToPresheaf _ _ ⋙ etaleSetInducedPresheaf.{u, v, z, w} hC hD X R ⋙ fibreFunctor G R

theorem etaleSetInducedSections_obj
    (F : Sheaf (equivariantEtaleTopology X) (ModuleCat.{max z w} R)) :
    haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
    (etaleSetInducedSections.{u, v, z, w} hC hD X R).obj F =
      fibreRep ((etaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj) :=
  rfl

/-- **Berkovich's formula** `Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G))`, étale case. -/
def etaleSetInducedSectionsIso
    (F : Sheaf (equivariantEtaleTopology X) (ModuleCat.{max z w} R)) :
    haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
    colimit ((basePoint G).op ⋙
        fibreDiagram ((etaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj)) ≅
      fibre ((etaleSetInducedPresheaf.{u, v, z, w} hC hD X R).obj F.obj) :=
  haveI := hasColimitsOfShape_pointedOrbit.{z, w} G R
  colimitOpenSubgroupIsoFibre _

/-- The étale and quasi-étale presheaves `γ_*F` agree on a sheaf restricted from `Qét(X(G))`
to `Ét(X(G))`. -/
theorem etaleSetInducedPresheaf_comp
    (F : (EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max z w} R) :
    (etaleSetInducedPresheaf hC hD X R).obj
        ((EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X).op ⋙ F) =
      (quasiEtaleSetInducedPresheaf hC hD X R).obj F :=
  rfl

end Etale

end Langlands.Sheaf.Equivariant.Analytic
