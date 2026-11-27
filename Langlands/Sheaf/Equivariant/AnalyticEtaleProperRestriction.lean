import Langlands.Sheaf.Equivariant.AnalyticEtaleInvariantPullback
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleSupport
import Langlands.Sheaf.Equivariant.AnalyticPointProductSupport
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper restriction of compactly supported analytic étale sections -/

noncomputable section

universe u v uL

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y} (hf : etale f)
  (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Restriction of an étale sheaf along an étale map, by postcomposition of its test maps. -/
abbrev etaleRestriction :=
  (EtaleSite.postcomposeEtale hf).sheafPushforwardContinuous
    (ModuleCat.{max u (v + 1) uL} R) (etaleTopology X) (etaleTopology Y)

private def restrictionToSelf : (EtaleSite.postcomposeEtale hf).obj (etaleSelf X) ⟶ etaleSelf Y :=
  etaleSelfIsTerminal.from _

/-- Global restriction of sections is evaluation on the map from the source test to the
identity test over the target. -/
def etaleSectionsRestriction :
    etaleSections.{u, v, uL} Y R ⟶ etaleRestriction.{u, v, uL} hf R ⋙ etaleSections.{u, v, uL} X R where
  app F := F.obj.map (restrictionToSelf hf).op
  naturality _ _ g := (g.hom.naturality (restrictionToSelf hf).op).symm

variable (Lₓ Lᵧ : Type uL) [NormedField Lₓ] [NormedAlgebra K Lₓ]
  [NormedField Lᵧ] [NormedAlgebra K Lᵧ]
  [T2Space (localizedSpaceFunctor.obj X)] [T2Space (localizedSpaceFunctor.obj Y)]
  (hX : ∀ x : (localizedFieldPointFunctor Lₓ).obj X, EtaleSite.PointAxioms Lₓ x)
  (hY : ∀ y : (localizedFieldPointFunctor Lᵧ).obj Y, EtaleSite.PointAxioms Lᵧ y)
  (surjX : Function.Surjective (pointProjection Lₓ X))
  (surjY : Function.Surjective (pointProjection Lᵧ Y))

include surjX surjY in
/-- Support on the source of an étale restriction is contained in the inverse image of
support on the target. Vanishing on an étale neighborhood descends to its open image;
restriction then vanishes on the inverse open. -/
theorem etaleRestriction_support_subset
    (F : Sheaf (etaleTopology Y) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf Y))) :
    etaleUnderlyingSupport Lₓ hX ((etaleRestriction.{u, v, uL} hf R).obj F).obj
        ((etaleSectionsRestriction.{u, v, uL} hf R).app F s) ⊆
      (localizedSpaceFunctor.map f) ⁻¹' etaleUnderlyingSupport Lᵧ hY F.obj s := by
  intro x hx
  by_contra hfx
  obtain ⟨V, a, hv, hz⟩ := (not_mem_etaleUnderlyingSupport_iff Lᵧ hY
    (etalePointLifting_of_hausdorff Lᵧ hY) surjY F.obj s (localizedSpaceFunctor.map f x)).mp hfx
  let U : Opens (localizedSpaceFunctor.obj Y) :=
    ⟨Set.range (localizedSpaceFunctor.map V.hom), (etaleOpenMap K V.hom V.prop).isOpen_range⟩
  let W : Opens (localizedSpaceFunctor.obj X) := (Opens.map (localizedSpaceFunctor.map f)).obj U
  let A := openEtaleObject X W
  let E := EtaleSite.postcomposeEtale hf
  have hU : F.obj.map (openEtaleToSelf Y U).op s = 0 := restriction_open_image_eq_zero.{u, v, uL} F s V a hz
  have hAW (z : localizedSpaceFunctor.obj (E.obj A).left) :
      localizedSpaceFunctor.map (E.obj A).hom z ∈ U := by
    change localizedSpaceFunctor.map (A.hom ≫ f) z ∈ U
    rw [Functor.map_comp, TopCat.comp_app]
    exact (mem_open_of_openEtale_hom X (𝟙 A) z)
  let b := openEtaleLift Y U (E.obj A) hAW
  have hcomp : E.map (openEtaleToSelf X W) ≫ restrictionToSelf hf = b ≫ openEtaleToSelf Y U :=
    etaleSelfIsTerminal.hom_ext _ _
  have hzero : ((etaleRestriction.{u, v, uL} hf R).obj F).obj.map (openEtaleToSelf X W).op
      ((etaleSectionsRestriction.{u, v, uL} hf R).app F s) = 0 := by
    change F.obj.map (E.map (openEtaleToSelf X W)).op (F.obj.map (restrictionToSelf hf).op s) = 0
    rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← op_comp, hcomp, op_comp, F.obj.map_comp,
      ModuleCat.comp_apply, hU, map_zero]
  have hxW : x ∈ Set.range (localizedSpaceFunctor.map A.hom) := ⟨⟨x, hv⟩, domainι_apply _ _⟩
  exact ((not_mem_etaleUnderlyingSupport_iff Lₓ hX
    (etalePointLifting_of_hausdorff Lₓ hX) surjX _ _ x).2
      ⟨A, openEtaleToSelf X W, hxW, hzero⟩) hx

include surjX surjY in
private theorem restrict_compactSupport (hp : IsProperMap (localizedSpaceFunctor.map f))
    (F : Sheaf (etaleTopology Y) (ModuleCat.{max u (v + 1) uL} R))
    (s : (etaleCompactSections Lᵧ hY R).obj F) :
    letI := pointTopology Lₓ X
    IsCompactlySupported (etalePoints Lₓ hX) ((etaleRestriction.{u, v, uL} hf R).obj F).obj
      ((etaleSectionsRestriction.{u, v, uL} hf R).app F s.val) := by
  let := pointTopology Lₓ X
  obtain ⟨D, hD, hsub⟩ := (exists_isCompact_superset_iff_of_surjective Lᵧ surjY _).mp s.property
  refine (exists_isCompact_superset_iff_of_surjective Lₓ surjX _).2
    ⟨_, hp.isCompact_preimage hD, ?_⟩
  exact (etaleRestriction_support_subset.{u, v, uL} hf R Lₓ Lᵧ hX hY surjX surjY F s.val).trans (Set.preimage_mono hsub)

/-- Restriction along an étale map which is proper on underlying analytic spaces maps
compactly supported sections to compactly supported sections. -/
def etaleCompactSectionsRestriction (hp : IsProperMap (localizedSpaceFunctor.map f)) :
    etaleCompactSections Lᵧ hY R ⟶ etaleRestriction.{u, v, uL} hf R ⋙ etaleCompactSections Lₓ hX R where
  app F := ModuleCat.ofHom (((etaleSectionsRestriction.{u, v, uL} hf R).app F).hom.restrict
    (fun s hs => restrict_compactSupport.{u, v, uL} hf R Lₓ Lᵧ hX hY surjX surjY hp F ⟨s, hs⟩))
  naturality F G a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((etaleSectionsRestriction.{u, v, uL} hf R).naturality a) s.val

/-- The map of compact sections is the ordinary étale restriction on their underlying sections. -/
@[simp] theorem etaleCompactSectionsRestriction_apply (hp : IsProperMap (localizedSpaceFunctor.map f))
    (F : Sheaf (etaleTopology Y) (ModuleCat.{max u (v + 1) uL} R))
    (s : (etaleCompactSections Lᵧ hY R).obj F) :
    ((etaleCompactSectionsRestriction.{u, v, uL} hf R Lₓ Lᵧ hX hY surjX surjY hp).app F s).val =
      (etaleSectionsRestriction.{u, v, uL} hf R).app F s.val := rfl

end Langlands.Sheaf.Equivariant.Analytic
