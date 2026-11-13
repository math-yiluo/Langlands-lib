import Langlands.Sheaf.Renard.SmoothProjectorActionSheaf

/-!
# Stalks of the original equivariant projector sheaf

The germ at a point of the original-vector global section `m ↦ (χ_W · m)_W`
is a surjective complex-linear map from the original module onto the actual
stalk. Its kernel consists of the vectors killed by the characteristic test of
some compact-open neighborhood. It intertwines the original module action with
stalk transport and is natural for the original module maps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.ProjectorActionStalks

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf
open Langlands.Sheaf.Renard.ProjectorActionSheaf

universe uG

variable {G : Type uG} [Group G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)
variable (M : CompatibleTestAction.{uG, 0, 0} G X)

/-- The germ at `x` of the original-vector global section of a module vector. -/
def originalGerm (x : X) :
    letI := M.complexModule
    M.module.obj →ₗ[ℂ] (CompactSections.ordinary (sheaf hX M).obj).stalk x :=
  letI := M.complexModule
  ((CompactSections.ordinary (sheaf hX M).obj).germ ⊤ x trivial).hom ∘ₗ
    ProjectorVectorSheaf.originalSection.{0, 0} hX M.module.property ⊤

theorem originalGerm_apply (x : X) (m : M.module.obj) :
    originalGerm hX M x m =
      (CompactSections.ordinary (sheaf hX M).obj).Γgerm x
        (ProjectorVectorSheaf.originalFamily hX ⊤ m) := rfl

/-- The original germ vanishes exactly when a compact-open neighborhood test kills the vector. -/
theorem originalGerm_eq_zero_iff (x : X) (m : M.module.obj) :
    originalGerm hX M x m = 0 ↔
      ∃ K : CompactOpen hX, x ∈ K.obj ∧ action hX M.module.obj K m = 0 := by
  rw [originalGerm_apply, CompactSections.germ_zero_iff]
  constructor
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨K, hxK, hKU⟩ := (compactOpenBasis hX).exists_subset U.openSet hxU
    refine ⟨K, hxK, ?_⟩
    have h0 := congrArg (fun s : ProjectorVectorSheaf.familySpace hX M.module.property
        U.openSet => (s.val ⟨K, hKU⟩).val)
      ((SmoothProjectorActionSheaf.restrict_originalFamily hX M U m).symm.trans hU)
    exact h0
  · rintro ⟨K, hxK, hK⟩
    refine ⟨⟨K.obj⟩, hxK, ?_⟩
    change ((transportPresheaf hX M).map
      (ActionOpens.inclusionHom (U := ⟨K.obj⟩) le_top).op).hom
        (ProjectorVectorSheaf.originalFamily hX ⊤ m) = 0
    rw [SmoothProjectorActionSheaf.restrict_originalFamily]
    apply BasisAllOpen.families_ext
    intro W
    apply Subtype.ext
    change action hX M.module.obj W.val m = 0
    rw [← action_absorb hX M.module.obj W.property m, hK, map_zero]

/-- Every germ of the reconstructed sheaf is the germ of an original-vector section. -/
theorem originalGerm_surjective (x : X) :
    Function.Surjective (originalGerm hX M x) := by
  intro t
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.exists_germ_eq (CompactSections.ordinary (sheaf hX M).obj) t
  obtain ⟨K, hxK, hKU⟩ := (compactOpenBasis hX).exists_subset U hxU
  refine ⟨(s.val ⟨K, hKU⟩).val, ?_⟩
  rw [← hs, ← TopCat.Presheaf.germ_res_apply (CompactSections.ordinary (sheaf hX M).obj)
    (homOfLE hKU) x hxK s]
  have hres := SmoothProjectorActionSheaf.restrict_family_eq_original hX M
    (U := ⟨U⟩) K hKU s
  have htop := SmoothProjectorActionSheaf.restrict_originalFamily hX M ⟨K.obj⟩
    (s.val ⟨K, hKU⟩).val
  rw [originalGerm_apply, ← TopCat.Presheaf.Γgerm_res_apply
    (CompactSections.ordinary (sheaf hX M).obj) (U := K.obj) (i := homOfLE le_top) x hxK]
  change (CompactSections.ordinary (sheaf hX M).obj).germ K.obj x hxK
      (((transportPresheaf hX M).map
        (ActionOpens.inclusionHom (U := ⟨K.obj⟩) le_top).op).hom
          (ProjectorVectorSheaf.originalFamily hX ⊤ (s.val ⟨K, hKU⟩).val)) =
    (CompactSections.ordinary (sheaf hX M).obj).germ K.obj x hxK
      (((transportPresheaf hX M).map
        (ActionOpens.inclusionHom (U := ⟨K.obj⟩) hKU).op).hom s)
  rw [htop, hres]

/-- Stalk transport of an original germ is the germ of the transported vector. -/
theorem stalkPull_originalGerm (q : G) (x : X) (hq : q⁻¹ • x = x) (m : M.module.obj) :
    (Godement.stalkPull (sheaf hX M).obj q⁻¹ x x hq).hom (originalGerm hX M x m) =
      originalGerm hX M x (M.action q m) := by
  rw [originalGerm_apply, originalGerm_apply,
    ← SmoothProjectorActionSheaf.global_originalFamily]
  exact congrArg (fun f => f.hom (ProjectorVectorSheaf.originalFamily hX ⊤ m))
    (Godement.germ_stalkPull_arrow (sheaf hX M).obj
      (ActionOpens.sectionArrow q) x x hq trivial)

variable {M} {N : CompatibleTestAction.{uG, 0, 0} G X}

/-- The original germ is natural for the original compatible module maps. -/
theorem stalkMap_originalGerm (φ : M ⟶ N) (x : X) (m : M.module.obj) :
    ((TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
        ((underlyingPresheaf G X (ModuleCat ℂ)).map (sheafMap hX φ).hom)).hom
        (originalGerm hX M x m) =
      originalGerm hX N x (CompatibleTestAction.moduleMap φ.moduleHom m) := by
  rw [originalGerm_apply, originalGerm_apply]
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply
    (⊤ : Opens (TopCat.of X)) x trivial
    ((underlyingPresheaf G X (ModuleCat ℂ)).map (sheafMap hX φ).hom)
    (ProjectorVectorSheaf.originalFamily hX ⊤ m)).trans ?_
  exact congrArg ((CompactSections.ordinary (sheaf hX N).obj).Γgerm x)
    (ProjectorVectorSheaf.sheafMap_originalSection.{0, 0} hX M.module.property
      N.module.property (CompatibleTestAction.moduleMap φ.moduleHom) ⊤ m)

end Langlands.Sheaf.Renard.ProjectorActionStalks
