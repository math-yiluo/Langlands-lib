import Langlands.Sheaf.ClopenExtensionLaws
import Langlands.Sheaf.CompactSupport
import Langlands.Topology.LocallyProfinite
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Compact global representatives of stalk elements

The map is the original global germ map restricted to compact sections.
Clopen zero extension supplies its representatives on a locally profinite base.
-/

noncomputable section

namespace Langlands.Sheaf.CompactGerms

open CategoryTheory TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- Forget only the scalar action, for the published additive zero extension. -/
abbrev additive (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F

/-- The published additive zero extension, with its original module carrier. -/
def extend (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (U : Opens X) (hU : IsClosed (U : Set X))
    (s : F.presheaf.obj (op U)) : F.presheaf.obj (op ⊤) :=
  ClopenExtension.extend (additive F) U hU s

/-- Restriction of zero extension recovers the given section. -/
theorem restrict_extend (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (U : Opens X) (hU : IsClosed (U : Set X)) (s : F.presheaf.obj (op U)) :
    F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (extend F U hU s) = s := by
  exact congrArg (fun f => f s) (ClopenExtension.extend_restrict (additive F) U hU)

/-- Zero extension has no nonzero germs outside its defining clopen. -/
theorem support_extend_subset (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (U : Opens X) (hU : IsClosed (U : Set X)) (s : F.presheaf.obj (op U)) :
    CompactSupport.support F.presheaf (extend F U hU s) ⊆ (U : Set X) := by
  intro x hx
  by_contra hxU
  have hzero : F.presheaf.map
      (homOfLE le_top : ClopenExtension.complement U hU ⟶ ⊤).op
      (extend F U hU s) = 0 :=
    congrArg (fun f => f s)
      (ClopenExtension.extend_restrict_complement (additive F) U hU)
  apply hx
  rw [← F.presheaf.Γgerm_res_apply x hxU (extend F U hU s)
    (i := homOfLE (show ClopenExtension.complement U hU ≤ ⊤ from le_top)), hzero]
  exact map_zero _

/-- Zero extension from a compact clopen defines an actual compact global section. -/
def compactExtension (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (U : Opens X) (hU : IsClosed (U : Set X)) (hc : IsCompact (U : Set X))
    (s : F.presheaf.obj (op U)) : CompactSupport.submodule F.presheaf :=
  ⟨extend F U hU s,
    hc.of_isClosed_subset (CompactSupport.isClosed_support _ _)
      (support_extend_subset F U hU s)⟩

/-- The original global germ map, restricted to the compact-section submodule. -/
def germ (F : TopCat.Sheaf (ModuleCat.{u} R) X) (x : X) :
    CompactSupport.submodule F.presheaf →ₗ[R] F.presheaf.stalk x :=
  (F.presheaf.Γgerm x).hom.comp (CompactSupport.submodule F.presheaf).subtype

@[simp]
theorem germ_apply (F : TopCat.Sheaf (ModuleCat.{u} R) X) (x : X)
    (s : CompactSupport.submodule F.presheaf) :
    germ F x s = F.presheaf.Γgerm x s.val := rfl

/-- Every original stalk element has a compactly supported global representative. -/
theorem germ_surjective (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (hX : Langlands.Topology.IsLocallyProfinite X) (x : X) :
    Function.Surjective (germ F x) := by
  let : T2Space X := hX.t2Space
  intro t
  obtain ⟨U, hxU, s, rfl⟩ := F.presheaf.exists_germ_eq t
  obtain ⟨V, hxV, hVo, hVc, hVU⟩ :=
    hX.hasCompactOpenNeighborhoodBasis x U (U.isOpen.mem_nhds hxU)
  let W : Opens X := ⟨V, hVo⟩
  let sW := F.presheaf.map (homOfLE hVU : W ⟶ U).op s
  refine ⟨compactExtension F W hVc.isClosed hVc sW, ?_⟩
  change F.presheaf.Γgerm x (extend F W hVc.isClosed sW) = _
  rw [← F.presheaf.Γgerm_res_apply x hxV (extend F W hVc.isClosed sW)
    (i := homOfLE (show W ≤ ⊤ from le_top)), restrict_extend]
  exact F.presheaf.germ_res_apply (homOfLE hVU : W ⟶ U) x hxV s

/-- Actual sheaf maps commute with the compact global germ maps. -/
theorem germ_naturality {F F' : TopCat.Sheaf (ModuleCat.{u} R) X}
    (f : F ⟶ F') (x : X) (s : CompactSupport.submodule F.presheaf) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f.hom (germ F x s) =
      germ F' x (CompactSupport.map f.hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial f.hom s.val

end Langlands.Sheaf.CompactGerms
