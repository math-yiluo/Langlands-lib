import Langlands.GroupScheme.Torus.Relative
import Mathlib.AlgebraicGeometry.Sites.Pretopology

/-! # Locality of the relative torus property -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

variable {S : Scheme.{u}} {G : GroupScheme S}

local instance : MorphismProperty.IsStableUnderComposition
    (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- The composite étale splitting cover of a group scheme which is a torus on
each member of a given étale cover. -/
def IsTorus.splittingCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hG : ∀ i, IsTorus ((GroupScheme.baseChange (𝒰.f i)).obj G)) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  𝒰.bind (fun i => (hG i).choose)

/-- A relative torus is detected on any étale cover of its base. -/
theorem IsTorus.of_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hG : ∀ i, IsTorus ((GroupScheme.baseChange (𝒰.f i)).obj G)) :
    IsTorus G := by
  choose 𝒱 h𝒱 using hG
  refine ⟨𝒰.bind 𝒱, fun ⟨i, j⟩ => ?_⟩
  change IsSplitTorus
    ((GroupScheme.baseChange ((𝒱 i).f j ≫ 𝒰.f i)).obj G)
  exact IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f i) ((𝒱 i).f j) G) (h𝒱 i j)

/-- The relative torus property is local on arbitrary Zariski open covers. -/
theorem IsTorus.of_openCover (𝒰 : Scheme.OpenCover.{u} S)
    (hG : ∀ i, IsTorus ((GroupScheme.baseChange (𝒰.f i)).obj G)) :
    IsTorus G :=
  IsTorus.of_etaleCover (𝒰.changeProp (Q := @Etale) (fun _ => inferInstance)) hG

/-- Relative-torus detection and preservation on a Zariski open cover. -/
theorem isTorus_iff_openCover (𝒰 : Scheme.OpenCover.{u} S) :
    IsTorus G ↔ ∀ i, IsTorus ((GroupScheme.baseChange (𝒰.f i)).obj G) :=
  ⟨fun h i => h.baseChange _, IsTorus.of_openCover 𝒰⟩

end Langlands.GroupScheme.RelativeTorus
