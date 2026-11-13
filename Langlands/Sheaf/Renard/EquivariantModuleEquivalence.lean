import Langlands.Sheaf.Renard.EquivariantModuleStatements
import Langlands.Sheaf.Renard.CompactSectionEquivalenceStatement
import Langlands.Sheaf.Renard.ModuleProjectorComparisonStatement

/-!
# Renard III.3.1: equivariant comparison maps and the conditional equivalences

The published II.2.5 comparisons `F ⟶ P(Γc F)` and `M ⟶ Γc(P M)` commute with
the original group operators. They therefore give natural transformations
between the identity functors and the composites of the published equivariant
compact-section and projector-action-sheaf functors. Their invertibility is
reduced to the two published II.2.5 isomorphism statements.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.EquivariantModuleEquivalence

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf
open Langlands.Sheaf.Renard.CompactSectionTestModule

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-! ### Germ transport of the original section action -/

/-- The original operator of `k⁻¹` on global sections pulls germs back along `k`. -/
theorem Γgerm_global_inv (F : ActionSheaf G X) (k : G)
    (t : F.obj.obj (op ActionOpens.top)) (x y : X) (h : k • x = y) :
    (CompactSections.ordinary F.obj).Γgerm x (globalRepresentation F k⁻¹ t) =
      (Godement.stalkPull F.obj k x y h).hom
        ((CompactSections.ordinary F.obj).Γgerm y t) := by
  let a : (ActionOpens.top : ActionOpens G X) ⟶ ActionOpens.top :=
    ⟨k, fun _ _ => trivial⟩
  have ha : ActionOpens.sectionArrow (X := X) k⁻¹ = a := by
    apply ActionOpens.Hom.ext
    simp [ActionOpens.sectionArrow, a]
  have hg := congrArg (fun f => f.hom t)
    (Godement.germ_stalkPull_arrow F.obj a x y h trivial)
  change (CompactSections.ordinary F.obj).Γgerm x
      (F.obj.map (ActionOpens.sectionArrow k⁻¹).op t) = _
  rw [ha]
  exact hg.symm

variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-! ### The equivariant sheaf-side comparison -/

/-- The II.2.5 family of zero extensions commutes with every labelled arrow. -/
theorem family_familyPull (F : ActionSheaf G X) {U V : ActionOpens G X} (f : U ⟶ V)
    (s : F.obj.obj (op V)) :
    SheafProjectorComparison.family (underlying F) hX (F.obj.map f.op s) =
      ProjectorActionSheaf.familyPull hX (CompactSectionActions.compatibleObject hX F) f
        (SheafProjectorComparison.family (underlying F) hX s) := by
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  apply SheafProjectorComparison.ext_compact (underlying F)
  intro x
  change (underlying F).presheaf.Γgerm x
      (SheafProjectorComparison.extension (underlying F) hX W.val W.property
        (F.obj.map f.op s) : (underlying F).presheaf.obj (op ⊤)) =
    (CompactSections.ordinary F.obj).Γgerm x (globalRepresentation F f.label⁻¹
      (SheafProjectorComparison.extension (underlying F) hX
        (ProjectorActionSheaf.translatedInside hX f W).val
        (ProjectorActionSheaf.translatedInside hX f W).property s :
          (underlying F).presheaf.obj (op ⊤)))
  rw [Γgerm_global_inv F f.label _ x (f.label • x) rfl]
  by_cases hx : x ∈ W.val.obj
  · have hy : f.label • x ∈ (ProjectorActionSheaf.translatedInside hX f W).val.obj := by
      change f.label⁻¹ • f.label • x ∈ W.val.obj
      rw [inv_smul_smul]
      exact hx
    rw [SheafProjectorComparison.Γgerm_extension_of_mem (underlying F) hX _ _ _ hx]
    erw [SheafProjectorComparison.Γgerm_extension_of_mem (underlying F) hX _ _ _ hy]
    have hg := congrArg (fun φ => φ.hom s)
      (Godement.germ_stalkPull_arrow F.obj f x (f.label • x) rfl (W.property hx))
    exact hg.symm
  · have hy : f.label • x ∉ (ProjectorActionSheaf.translatedInside hX f W).val.obj := by
      change ¬ f.label⁻¹ • f.label • x ∈ W.val.obj
      rw [inv_smul_smul]
      exact hx
    rw [SheafProjectorComparison.Γgerm_extension_of_not_mem (underlying F) hX _ _ _ hx]
    erw [SheafProjectorComparison.Γgerm_extension_of_not_mem (underlying F) hX _ _ _ hy]
    exact (map_zero _).symm

/-- The II.2.5 comparison `F ⟶ P(Γc F)` as an equivariant sheaf map. Its component on
every transport object is the published ordinary component on the same open. -/
def unitHom (F : ActionSheaf G X) :
    F ⟶ (ProjectorActionSheaf.functor hX).obj ((CompactSectionActions.functor hX).obj F) :=
  ObjectProperty.homMk
    { app U := SheafProjectorComparison.sheafComparisonApp (underlying F) hX U.unop.openSet
      naturality U V f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact family_familyPull hX F f.unop s }

/-- The components are literally those of the published ordinary comparison. -/
theorem unitHom_app (F : ActionSheaf G X) (U : (ActionOpens G X)ᵒᵖ) :
    (unitHom hX F).hom.app U =
      (SheafProjectorComparison.sheafComparison (underlying F) hX).hom.app
        (op U.unop.openSet) := rfl

/-- Naturality of the equivariant sheaf-side comparison. -/
def unitNat :
    𝟭 (ActionSheaf G X) ⟶
      CompactSectionActions.functor hX ⋙ ProjectorActionSheaf.functor (G := G) hX where
  app F := unitHom hX F
  naturality F F' φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (SheafProjectorComparison.familyMap_family hX
      ((toSheaf G X (ModuleCat.{0} ℂ)).map φ) s).symm

/-- The equivariant sheaf-side comparison is invertible when the ordinary one is. -/
theorem isIso_unitHom (F : ActionSheaf G X)
    [IsIso (SheafProjectorComparison.sheafComparison (underlying F) hX)] :
    IsIso (unitHom hX F) := by
  rw [← ObjectProperty.isIso_hom_iff]
  have happ : ∀ U : (ActionOpens G X)ᵒᵖ, IsIso ((unitHom hX F).hom.app U) := by
    intro U
    rw [unitHom_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-! ### The equivariant module-side comparison -/

/-- The II.2.5 comparison `M ⟶ Γc(P M)`, followed by the identity-component comparison of
the underlying sheaf of the reconstructed action sheaf with the published projector sheaf. -/
def counitInvModule (M : CompatibleTestAction.{uG, 0, 0} G X) :
    M.module ⟶ ((CompactSectionActions.functor hX).obj
      ((ProjectorActionSheaf.functor hX).obj M)).module :=
  ModuleProjectorComparison.moduleComparison hX M.module ≫
    (compactSectionFunctor hX).map (ProjectorActionSheaf.underlyingSheafIso hX M).inv

/-- The module-side comparison sends `m` to its original-vector global section. -/
theorem counitInvModule_val (M : CompatibleTestAction.{uG, 0, 0} G X) (m : M.module.obj) :
    Subtype.val (show CompactSupport.submodule
        (underlying ((ProjectorActionSheaf.functor hX).obj M)).presheaf from
      CompatibleTestAction.moduleMap (counitInvModule hX M) m) =
      ProjectorVectorSheaf.originalFamily hX ⊤ m := rfl

/-- The module-side comparison commutes with the original group operators. -/
theorem counitInvModule_comm (M : CompatibleTestAction.{uG, 0, 0} G X) (g : G)
    (m : M.module.obj) :
    CompatibleTestAction.moduleMap (counitInvModule hX M) (M.action g m) =
      ((CompactSectionActions.functor hX).obj ((ProjectorActionSheaf.functor hX).obj M)).action g
        (CompatibleTestAction.moduleMap (counitInvModule hX M) m) := by
  apply Subtype.ext
  exact (SmoothProjectorActionSheaf.global_originalFamily hX M g m).symm

/-- The module-side comparison as a morphism of compatible test actions. -/
def counitInvHom (M : CompatibleTestAction.{uG, 0, 0} G X) :
    M ⟶ (CompactSectionActions.functor hX).obj ((ProjectorActionSheaf.functor hX).obj M) :=
  ⟨counitInvModule hX M, counitInvModule_comm hX M⟩

/-- Naturality of the equivariant module-side comparison. -/
def counitInvNat :
    𝟭 (CompatibleTestAction.{uG, 0, 0} G X) ⟶
      ProjectorActionSheaf.functor (G := G) hX ⋙ CompactSectionActions.functor hX where
  app M := counitInvHom hX M
  naturality M N φ := by
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    apply Subtype.ext
    apply BasisAllOpen.families_ext
    intro U
    apply Subtype.ext
    exact (φ.moduleHom.hom.map_smul (test hX U.val) m).symm

/-- A compatible-action map whose original module map is invertible is invertible. -/
theorem isIso_of_isIso_moduleHom {M N : CompatibleTestAction.{uG, 0, 0} G X} (f : M ⟶ N)
    [hf : IsIso f.moduleHom] : IsIso f := by
  let e := asIso f.moduleHom
  have h1 : ∀ x : M.module.obj,
      CompatibleTestAction.moduleMap e.inv (CompatibleTestAction.moduleMap f.moduleHom x) = x :=
    fun x => congrArg (fun φ => CompatibleTestAction.moduleMap φ x) e.hom_inv_id
  have h2 : ∀ y : N.module.obj,
      CompatibleTestAction.moduleMap f.moduleHom (CompatibleTestAction.moduleMap e.inv y) = y :=
    fun y => congrArg (fun φ => CompatibleTestAction.moduleMap φ y) e.inv_hom_id
  let finv : N ⟶ M := ⟨e.inv, fun g n => by
    conv_lhs => rw [← h2 n]
    rw [← f.comm, h1]⟩
  exact ⟨⟨finv, CompatibleTestAction.Hom.ext e.hom_inv_id,
    CompatibleTestAction.Hom.ext e.inv_hom_id⟩⟩

/-- The equivariant module-side comparison is invertible when the ordinary one is. -/
theorem isIso_counitInvHom (M : CompatibleTestAction.{uG, 0, 0} G X)
    [IsIso (ModuleProjectorComparison.moduleComparison hX M.module)] :
    IsIso (counitInvHom hX M) := by
  have : IsIso (counitInvModule hX M) := by
    unfold counitInvModule
    infer_instance
  have h' : IsIso (counitInvHom hX M).moduleHom := this
  exact isIso_of_isIso_moduleHom (counitInvHom hX M) (hf := h')

/-! ### The conditional equivalences -/

section Conditional

variable (hS : CompactSectionEquivalence.SheafComparisonIsIso)
variable (hM : ModuleProjectorComparison.ModuleComparisonIsIso)

include hS in
theorem isIso_unitNat : IsIso (unitNat (G := G) hX) := by
  have : ∀ F : ActionSheaf G X, IsIso ((unitNat hX).app F) := by
    intro F
    have := hS X hX (underlying F)
    exact isIso_unitHom hX F
  exact NatIso.isIso_of_isIso_app _

include hM in
theorem isIso_counitInvNat : IsIso (counitInvNat (G := G) hX) := by
  have : ∀ M : CompatibleTestAction.{uG, 0, 0} G X, IsIso ((counitInvNat hX).app M) := by
    intro M
    have := hM X hX M.module
    exact isIso_counitInvHom hX M
  exact NatIso.isIso_of_isIso_app _

/-- The algebraic III.3.1 equivalence with the exact published functors. -/
def equivalence : ActionSheaf G X ≌ CompatibleTestAction.{uG, 0, 0} G X :=
  haveI := isIso_unitNat (G := G) hX hS
  haveI := isIso_counitInvNat (G := G) hX hM
  CategoryTheory.Equivalence.mk (CompactSectionActions.functor hX) (ProjectorActionSheaf.functor hX)
    (asIso (unitNat hX)) (asIso (counitInvNat hX)).symm

theorem equivalence_functor :
    (equivalence (G := G) hX hS hM).functor = CompactSectionActions.functor hX := rfl

theorem equivalence_inverse :
    (equivalence (G := G) hX hS hM).inverse = ProjectorActionSheaf.functor hX := rfl

variable [IsTopologicalGroup G] (hG : Langlands.Topology.IsLocallyProfinite G)

/-- The unit restricted to the whole-module smooth subcategories. -/
def smoothUnitIso :
    𝟭 (SmoothActionSheaf G X) ≅
      CompactSectionActions.smoothFunctor hX ⋙ SmoothProjectorActionSheaf.smoothFunctor hX hG :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ ((equivalence (G := G) hX hS hM).unitIso.app F.obj))
    (fun φ => by
      apply ObjectProperty.hom_ext
      exact (equivalence (G := G) hX hS hM).unitIso.hom.naturality φ.hom)

/-- The counit restricted to the whole-module smooth subcategories. -/
def smoothCounitIso :
    SmoothProjectorActionSheaf.smoothFunctor hX hG ⋙ CompactSectionActions.smoothFunctor hX ≅
      𝟭 (CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := X)) :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((equivalence (G := G) hX hS hM).counitIso.app M.obj))
    (fun φ => by
      apply ObjectProperty.hom_ext
      exact (equivalence (G := G) hX hS hM).counitIso.hom.naturality φ.hom)

/-- The smooth III.3.2 equivalence with the exact published smooth functors. -/
def smoothEquivalence :
    SmoothActionSheaf G X ≌ CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := X) :=
  CategoryTheory.Equivalence.mk (CompactSectionActions.smoothFunctor hX)
    (SmoothProjectorActionSheaf.smoothFunctor hX hG)
    (smoothUnitIso hX hS hM hG) (smoothCounitIso hX hS hM hG)

end Conditional

/-- Renard III.3.1–III.3.2, conditional on the two published II.2.5 comparison
isomorphism statements. -/
theorem statements_of_comparisons
    (hS : CompactSectionEquivalence.SheafComparisonIsIso)
    (hM : ModuleProjectorComparison.ModuleComparisonIsIso) :
    EquivariantModuleStatements.Statements.{uG} := by
  refine ⟨?_, ?_⟩
  · intro G _ _ _ _ X _ _ _ hX
    exact ⟨equivalence hX hS hM, rfl, rfl⟩
  · intro G _ _ _ hG X _ _ _ hX
    exact ⟨smoothEquivalence hX hS hM hG, rfl, rfl⟩

end Langlands.Sheaf.Renard.EquivariantModuleEquivalence
