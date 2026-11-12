import Langlands.Sheaf.Renard.SmoothStalkRestriction
import Langlands.Representation.Geometric.CosetAction
import Langlands.Representation.Induction.Definitions

/-!
# Renard's homogeneous base and section-to-induction maps

The base is the published left quotient with inverse right action, and the
coefficient space is the original stalk at the identity coset.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousSections

open CategoryTheory Opposite
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Induction

universe uG

section Base

variable {G : Type uG} [Group G] (H : Subgroup G)

/-- The published inverse right action, restricted from the top subgroup to `G`. -/
@[instance_reducible]
def homogeneousAction : MulAction G (LeftQuotient H) :=
  letI := Langlands.Geometric.leftQuotientAction H (⊤ : Subgroup G)
  MulAction.compHom _ (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom

attribute [local instance] homogeneousAction

@[simp]
theorem smul_quotientMap (g k : G) :
    g • quotientMap H k = quotientMap H (k * g⁻¹) := rfl

/-- The identity coset of the actual left quotient. -/
def origin : LeftQuotient H := quotientMap H 1

/-- Every element of `H` fixes the identity coset under the original action. -/
theorem subgroup_fixes_origin (h : H) : (h : G) • origin H = origin H := by
  change quotientMap H (1 * (h : G)⁻¹) = quotientMap H 1
  apply Quotient.sound (s := QuotientGroup.rightRel H)
  exact QuotientGroup.rightRel_apply.mpr (by simpa only [one_mul, inv_inv] using h.property)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Joint continuity is inherited from the existing top-subgroup quotient action. -/
instance homogeneousContinuousSMul : ContinuousSMul G (LeftQuotient H) := by
  let := Langlands.Geometric.leftQuotientAction H (⊤ : Subgroup G)
  let := Langlands.Geometric.leftQuotientAction_continuousSMul H (⊤ : Subgroup G)
  exact MulAction.continuousSMul_compHom
    (show Continuous (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm from
      continuous_id.subtype_mk _)

/-- A closed-subgroup left quotient retains the source's Hausdorff compact-open basis. -/
theorem quotient_isLocallyProfinite
    (hG : Langlands.Topology.IsLocallyProfinite G) (hH : IsClosed (H : Set G)) :
    Langlands.Topology.IsLocallyProfinite (LeftQuotient H) := by
  refine ⟨Langlands.QuotientIntegration.leftQuotient_t2Space H hH, ?_⟩
  intro x U hU
  induction x using Quotient.inductionOn with
  | h g =>
    have hpre : quotientMap H ⁻¹' U ∈ nhds g :=
      ((Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap H).continuous.continuousAt).preimage_mem_nhds hU
    obtain ⟨V, hgV, hVo, hVc, hVU⟩ := hG.hasCompactOpenNeighborhoodBasis g _ hpre
    refine ⟨quotientMap H '' V, ⟨g, hgV, rfl⟩,
      (Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap H).isOpenMap _ hVo,
      hVc.image continuous_quotient_mk', ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact hVU hk

end Base

attribute [local instance] homogeneousAction

section Sections

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

/-- The coefficient representation is the action on the original identity-coset stalk. -/
abbrev stalkRepresentation (F : ActionSheaf G (LeftQuotient H)) :=
  ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).obj F).ρ

/-- The source's literal formula `α(s)(g) = germ_o(γ_g(s))` on all global sections. -/
def alphaFunction (F : ActionSheaf G (LeftQuotient H))
    (s : F.obj.obj (op ActionOpens.top)) (g : G) :
    (CompactSections.ordinary F.obj).stalk (origin H) :=
  (CompactSections.ordinary F.obj).Γgerm (origin H) (globalRepresentation F g s)

/-- Stalk transport makes the literal formula covariant under `H`. -/
theorem alphaFunction_covariant (F : ActionSheaf G (LeftQuotient H))
    (s : F.obj.obj (op ActionOpens.top)) (h : H) (g : G) :
    alphaFunction H F s ((h : G) * g) =
      stalkRepresentation H F h (alphaFunction H F s g) := by
  rw [alphaFunction, global_mul]
  exact (congrArg (fun f => f.hom (globalRepresentation F g s))
    (Godement.germ_stalkPull_arrow F.obj
      (ActionOpens.sectionArrow (h : G)) (origin H) (origin H)
      (subgroup_fixes_origin H h⁻¹) trivial)).symm

/-- The actual map into Mathlib's covariant-function module. -/
def alphaEquivariant (F : ActionSheaf G (LeftQuotient H)) :
    F.obj.obj (op ActionOpens.top) →ₗ[ℂ]
      EquivariantFunctions H (stalkRepresentation H F) where
  toFun s := ⟨alphaFunction H F s, alphaFunction_covariant H F s⟩
  map_add' s t := by
    apply Subtype.ext
    funext g
    simp [alphaFunction]
  map_smul' c s := by
    apply Subtype.ext
    funext g
    simp [alphaFunction]

/-- The literal formula intertwines the original global and right-translation actions. -/
def alphaGlobal (F : ActionSheaf G (LeftQuotient H)) :
    (globalRepresentation F).IntertwiningMap
      (equivariantAction H (stalkRepresentation H F)) where
  toLinearMap := alphaEquivariant H F
  isIntertwining' k := by
    ext s g
    change alphaFunction H F (globalRepresentation F k s) g =
      alphaFunction H F s (g * k)
    simp only [alphaFunction, global_mul]

/-- Restrict the literal global map to smooth global sections and smooth induction. -/
def alphaSmoothGlobal (F : ActionSheaf G (LeftQuotient H)) :
    (Langlands.smoothPart (globalRepresentation F)).IntertwiningMap
      (smoothInduced H (stalkRepresentation H F)) :=
  Langlands.smoothMap (alphaGlobal H F)

/-- The same formula on the actual compact-section representation. -/
def alphaCompactEquivariant (F : ActionSheaf G (LeftQuotient H)) :
    (compactRepresentation F).IntertwiningMap
      (equivariantAction H (stalkRepresentation H F)) :=
  (alphaGlobal H F).comp ((CompactSections.inclusion ℂ G (LeftQuotient H)).app F).hom

/-- Renard smoothness puts the images of all compact sections in actual smooth induction. -/
def alphaCompactToSmooth (F : SmoothActionSheaf G (LeftQuotient H)) :
    (compactRepresentation F.obj).IntertwiningMap
      (smoothInduced H (stalkRepresentation H F.obj)) :=
  Langlands.smoothLift F.property (alphaCompactEquivariant H F.obj)

/-- Nonzero induced values are precisely the original nonzero germs at the same coset. -/
theorem alphaFunction_ne_zero_iff (F : ActionSheaf G (LeftQuotient H))
    (s : F.obj.obj (op ActionOpens.top)) (g : G) :
    alphaFunction H F s g ≠ 0 ↔
      (CompactSections.ordinary F.obj).Γgerm (quotientMap H g) s ≠ 0 := by
  constructor
  · intro ha hs
    apply ha
    apply CompactSections.germ_action_zero F.obj g s (origin H)
    rw [origin, smul_quotientMap, inv_inv, one_mul]
    exact hs
  · intro hs ha
    have hz := CompactSections.germ_action_zero F.obj g⁻¹
      (globalRepresentation F g s) (quotientMap H g) (by
        rw [inv_inv, smul_quotientMap, mul_inv_cancel]
        exact ha)
    change (CompactSections.ordinary F.obj).Γgerm (quotientMap H g)
      (globalRepresentation F g⁻¹ (globalRepresentation F g s)) = 0 at hz
    rw [Representation.inv_self_apply] at hz
    exact hs hz

/-- Projected nonzero support of the literal induced function is exactly original germ support. -/
theorem quotientSupport_alphaFunction (F : ActionSheaf G (LeftQuotient H))
    (s : F.obj.obj (op ActionOpens.top)) :
    quotientSupport H (alphaFunction H F s) =
      Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F.obj) s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact (alphaFunction_ne_zero_iff H F s g).1 hg
  · intro x
    induction x using Quotient.inductionOn with
    | h g =>
      intro hg
      exact ⟨g, (alphaFunction_ne_zero_iff H F s g).2 hg, rfl⟩

/-- The literal compact-section map lands in the published compact-induced representation. -/
def alphaCompact (F : SmoothActionSheaf G (LeftQuotient H)) :
    (compactRepresentation F.obj).IntertwiningMap
      (compactInduced H (stalkRepresentation H F.obj)) where
  toLinearMap := (alphaCompactToSmooth H F).toLinearMap.codRestrict
    (compactFunctions H (stalkRepresentation H F.obj)) (by
      intro s
      change IsCompact (quotientSupport H (alphaFunction H F.obj s.val))
      rw [quotientSupport_alphaFunction]
      exact s.property)
  isIntertwining' k := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact LinearMap.congr_fun ((alphaCompactToSmooth H F).isIntertwining' k) s

/-- Evaluation of the constructed compact map is the literal source formula. -/
theorem alphaCompact_apply (F : SmoothActionSheaf G (LeftQuotient H))
    (s : Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj.obj))
    (g : G) :
    eval H (stalkRepresentation H F.obj) (alphaCompact H F s).val g =
      alphaFunction H F.obj s.val g := rfl

/-- Evaluation of the smooth-global map is the same formula. -/
theorem alphaSmoothGlobal_apply (F : ActionSheaf G (LeftQuotient H))
    (s : Langlands.smoothVectors (globalRepresentation F)) (g : G) :
    eval H (stalkRepresentation H F) (alphaSmoothGlobal H F s) g =
      alphaFunction H F s.val g := rfl

/-- Naturality of the literal formula uses the actual induced stalk map. -/
theorem alphaFunction_naturality {F F' : ActionSheaf G (LeftQuotient H)}
    (f : F ⟶ F') (s : F.obj.obj (op ActionOpens.top)) (g : G) :
    ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map f).hom
        (alphaFunction H F s g) =
      alphaFunction H F' ((f.hom.app (op ActionOpens.top)).hom s) g := by
  have hg := congrArg (fun k => k.hom s)
    (f.hom.naturality (ActionOpens.sectionArrow g).op)
  have hx := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (⊤ : TopologicalSpace.Opens (TopCat.of (LeftQuotient H))) (origin H) trivial
    ((underlyingPresheaf G (LeftQuotient H) (ModuleCat ℂ)).map f.hom)
    (globalRepresentation F g s)
  exact hx.trans (congrArg ((CompactSections.ordinary F'.obj).Γgerm (origin H)) hg)

/-- Naturality of the actual compact-induction map. -/
theorem alphaCompact_naturality {F F' : SmoothActionSheaf G (LeftQuotient H)}
    (f : F ⟶ F') :
    (compactInducedMap H
        ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map f.hom).hom).comp
        (alphaCompact H F) =
      (alphaCompact H F').comp (CompactSections.map f.hom) := by
  ext s g
  exact alphaFunction_naturality H f.hom s.val g

/-- Naturality after restricting global sections to their actual smooth part. -/
theorem alphaSmoothGlobal_naturality {F F' : ActionSheaf G (LeftQuotient H)}
    (f : F ⟶ F') :
    (smoothInducedMap H
        ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map f).hom).comp
        (alphaSmoothGlobal H F) =
      (alphaSmoothGlobal H F').comp
        (Langlands.smoothMap ((sectionRepresentation ℂ G (LeftQuotient H)).map f).hom) := by
  ext s g
  exact alphaFunction_naturality H f s.val g

/-- Smooth point restriction on the actual homogeneous base. -/
def pointRestriction (hG : Langlands.Topology.IsLocallyProfinite G)
    (hH : IsClosed (H : Set G)) :
    SmoothActionSheaf G (LeftQuotient H) ⥤ Langlands.SmoothRep.{0, 0, 0} ℂ H :=
  smoothFixedStalkFunctor H (origin H) (subgroup_fixes_origin H)
    (quotient_isLocallyProfinite H hG hH)

end Sections

end Langlands.Sheaf.Renard.HomogeneousSections
