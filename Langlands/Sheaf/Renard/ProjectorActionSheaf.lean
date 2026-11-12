import Langlands.Sheaf.Renard.ProjectorVectorSheafSections
import Langlands.Sheaf.Renard.CompatibleTestActions
import Langlands.Sheaf.Renard.SectionActions

/-!
# Group actions on the original complex projector sheaf

A compatible test-module action transports the original compact-open
projector ranges and their compatible families, with inverse group labels.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.ProjectorActionSheaf

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf

universe uG

variable {G : Type uG} [Group G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-- Translate an original compact open by the original base action. -/
def translateCompact (g : G) (W : CompactOpen hX) : CompactOpen hX :=
  ⟨(ActionOpens.translate g (⟨W.obj⟩ : ActionOpens G X)).openSet, by
    have heq : (fun x : X => g • x) '' (W.obj : Set X) =
        {x : X | g⁻¹ • x ∈ W.obj} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨g⁻¹ • x, hx, smul_inv_smul g x⟩
    change IsCompact {x : X | g⁻¹ • x ∈ W.obj}
    rw [← heq]
    exact (compact hX W).image (continuous_const_smul g)⟩

@[simp]
theorem mem_translateCompact (g : G) (W : CompactOpen hX) (x : X) :
    x ∈ (translateCompact hX g W).obj ↔ g⁻¹ • x ∈ W.obj := Iff.rfl

@[simp]
theorem translateCompact_one (W : CompactOpen hX) :
    translateCompact hX (1 : G) W = W := by
  apply ObjectProperty.FullSubcategory.ext
  ext x
  simp

/-- Translation preserves inclusion of the actual compact opens. -/
theorem translateCompact_mono (g : G) {W T : CompactOpen hX} (h : W.obj ≤ T.obj) :
    (translateCompact hX g W).obj ≤ (translateCompact hX g T).obj :=
  fun _ hx => h hx

/-- The group product acts on the same compact-open carrier. -/
theorem translateCompact_mul (g k : G) (W : CompactOpen hX) :
    translateCompact hX (g * k) W =
      translateCompact hX g (translateCompact hX k W) := by
  apply ObjectProperty.FullSubcategory.ext
  ext x
  simp [mul_inv_rev, mul_smul]

/-- The original characteristic test translates to that of the translated open. -/
theorem test_translate (g : G) (W : CompactOpen hX) :
    testRepresentation g (test hX W) = test hX (translateCompact hX g W) := by
  classical
  ext x
  rfl

/-- Inverse translation brings the original projector back to the original open. -/
theorem test_inverse_translate (g : G) (W : CompactOpen hX) :
    testRepresentation g⁻¹ (test hX (translateCompact hX g W)) = test hX W := by
  classical
  ext x
  simp only [testRepresentation_apply, inv_inv]
  change (if g⁻¹ • (g • x) ∈ W.obj then (1 : ℂ) else 0) =
    (if x ∈ W.obj then (1 : ℂ) else 0)
  rw [inv_smul_smul]

variable (M : CompatibleTestAction.{uG, 0, 0} G X)

/-- An inverse-labelled group operator transports the original projector range. -/
def valuePull (g : G) (W : CompactOpen hX)
    (s : Value hX M.module.obj (translateCompact hX g W)) : Value hX M.module.obj W :=
  ⟨M.action g⁻¹ s.val, by
    change test hX W • M.action g⁻¹ s.val = M.action g⁻¹ s.val
    calc
      test hX W • M.action g⁻¹ s.val =
          M.action g⁻¹ (test hX (translateCompact hX g W) • s.val) := by
        rw [M.compatible, test_inverse_translate]
      _ = M.action g⁻¹ s.val := congrArg (M.action g⁻¹) s.property⟩

/-- Projector restriction and inverse-labelled transport commute. -/
theorem valuePull_restrict (g : G) {W T : CompactOpen hX} (h : W.obj ≤ T.obj)
    (s : Value hX M.module.obj (translateCompact hX g T)) :
    restrict hX M.module.obj h (valuePull hX M g T s) =
      valuePull hX M g W
        (restrict hX M.module.obj (translateCompact_mono hX g h) s) := by
  apply Subtype.ext
  change test hX W • M.action g⁻¹ s.val =
    M.action g⁻¹ (test hX (translateCompact hX g W) • s.val)
  rw [M.compatible, test_inverse_translate]

/-- The same transport is complex-linear for the published projector scalars. -/
def valuePullLinear (g : G) (W : CompactOpen hX) :
    letI := ProjectorVectorSheaf.valueModule hX M.module.property (translateCompact hX g W)
    letI := ProjectorVectorSheaf.valueModule hX M.module.property W
    Value hX M.module.obj (translateCompact hX g W) →ₗ[ℂ] Value hX M.module.obj W :=
  letI := M.complexModule
  letI := ProjectorVectorSheaf.valueModule hX M.module.property (translateCompact hX g W)
  letI := ProjectorVectorSheaf.valueModule hX M.module.property W
  { toFun := valuePull hX M g W
    map_add' := fun s t => Subtype.ext (map_add (M.action g⁻¹) s.val t.val)
    map_smul' := fun c s => Subtype.ext (map_smul (M.action g⁻¹) c s.val) }

/-- Translate a compact component into the target of an actual labelled arrow. -/
def translatedInside {U V : ActionOpens G X} (f : U ⟶ V)
    (W : BasisAllOpen.Inside (compactOpenBasis hX) U.openSet) :
    BasisAllOpen.Inside (compactOpenBasis hX) V.openSet :=
  ⟨translateCompact hX f.label W.val, by
    intro x hx
    have hi := f.mapsTo (f.label⁻¹ • x) (W.property hx)
    simpa using hi⟩

/-- Pull a published compatible projector family along an actual labelled arrow. -/
def familyPull {U V : ActionOpens G X} (f : U ⟶ V)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property V.openSet) :
    ProjectorVectorSheaf.familySpace hX M.module.property U.openSet :=
  ⟨fun W => valuePull hX M f.label W.val (s.val (translatedInside hX f W)), by
    intro W T h
    change restrict hX M.module.obj h
      (valuePull hX M f.label W.val (s.val (translatedInside hX f W))) =
        valuePull hX M f.label T.val (s.val (translatedInside hX f T))
    erw [valuePull_restrict]
    exact congrArg (valuePull hX M f.label T.val)
      (s.property (translatedInside hX f W) (translatedInside hX f T)
        (translateCompact_mono hX f.label h))⟩

/-- The transported family has the literal original-module component formula. -/
theorem familyPull_val {U V : ActionOpens G X} (f : U ⟶ V)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property V.openSet)
    (W : BasisAllOpen.Inside (compactOpenBasis hX) U.openSet) :
    ((familyPull hX M f s).val W).val =
      M.action f.label⁻¹ (s.val (translatedInside hX f W)).val := rfl

/-- The original family transport is complex-linear. -/
def familyPullLinear {U V : ActionOpens G X} (f : U ⟶ V) :
    ProjectorVectorSheaf.familySpace hX M.module.property V.openSet ⟶
      ProjectorVectorSheaf.familySpace hX M.module.property U.openSet :=
  letI := M.complexModule
  letI := ProjectorVectorSheaf.familyModule hX M.module.property V.openSet
  letI := ProjectorVectorSheaf.familyModule hX M.module.property U.openSet
  ModuleCat.ofHom
    { toFun := familyPull hX M f
      map_add' := fun s t => by
        apply BasisAllOpen.families_ext
        intro W
        apply Subtype.ext
        exact map_add (M.action f.label⁻¹) _ _
      map_smul' := fun c s => by
        apply BasisAllOpen.families_ext
        intro W
        apply Subtype.ext
        exact map_smul (M.action f.label⁻¹) c _ }

/-- The identity arrow keeps the actual compact component. -/
theorem translatedInside_id (U : ActionOpens G X)
    (W : BasisAllOpen.Inside (compactOpenBasis hX) U.openSet) :
    translatedInside hX (𝟙 U) W = W := by
  apply Subtype.ext
  exact translateCompact_one hX W.val

/-- Composition translates the same compact component successively. -/
theorem translatedInside_comp {U V T : ActionOpens G X} (f : U ⟶ V) (k : V ⟶ T)
    (W : BasisAllOpen.Inside (compactOpenBasis hX) U.openSet) :
    translatedInside hX (f ≫ k) W =
      translatedInside hX k (translatedInside hX f W) := by
  apply Subtype.ext
  exact translateCompact_mul hX k.label f.label W.val

/-- Pulling an original family along the identity changes no vector. -/
theorem familyPull_id (U : ActionOpens G X)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property U.openSet) :
    familyPull hX M (𝟙 U) s = s := by
  let := M.complexModule
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  change M.action (1 : G)⁻¹ (s.val (translatedInside hX (𝟙 U) W)).val = (s.val W).val
  rw [inv_one, translatedInside_id]
  exact LinearMap.congr_fun (map_one M.action) _

/-- Pulling families respects actual labelled-arrow composition. -/
theorem familyPull_comp {U V T : ActionOpens G X} (f : U ⟶ V) (k : V ⟶ T)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property T.openSet) :
    familyPull hX M (f ≫ k) s = familyPull hX M f (familyPull hX M k s) := by
  let := M.complexModule
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  change M.action (k.label * f.label)⁻¹
      (s.val (translatedInside hX (f ≫ k) W)).val =
    M.action f.label⁻¹ (M.action k.label⁻¹
      (s.val (translatedInside hX k (translatedInside hX f W))).val)
  rw [translatedInside_comp, mul_inv_rev]
  exact LinearMap.congr_fun (map_mul M.action f.label⁻¹ k.label⁻¹) _

/-- The published family spaces with all actual equivariant restriction maps. -/
def transportPresheaf : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ProjectorVectorSheaf.familySpace hX M.module.property U.unop.openSet
  map f := familyPullLinear hX M f.unop
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact familyPull_id hX M U.unop s
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact familyPull_comp hX M g.unop f.unop s

/-- Ordinary inclusions retain exactly the original family restrictions. -/
theorem familyPull_inclusion {U V : Opens X} (i : U ⟶ V)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property V) :
    familyPull hX M ((ActionOpens.inclusion G X).map i) s =
      (ProjectorVectorSheaf.presheaf hX M.module.property).map i.op s := by
  let := M.complexModule
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  have hW : translatedInside hX ((ActionOpens.inclusion G X).map i) W =
      ⟨W.val, W.property.trans i.le⟩ := by
    apply Subtype.ext
    exact translateCompact_one hX W.val
  change M.action (1 : G)⁻¹
      (s.val (translatedInside hX ((ActionOpens.inclusion G X).map i) W)).val =
    (s.val ⟨W.val, W.property.trans i.le⟩).val
  rw [hW, inv_one]
  exact LinearMap.congr_fun (map_one M.action) _

/-- Forgetting labels gives the original projector sheaf presheaf by identity components. -/
def underlyingIso :
    (underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj (transportPresheaf hX M) ≅
      ProjectorVectorSheaf.presheaf hX M.module.property :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact familyPull_inclusion hX M f.unop s)

/-- The original underlying projector sheaf supplies the sheaf condition. -/
theorem isSheaf :
    ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj
      (transportPresheaf hX M)).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iso_iff (underlyingIso hX M)).2
    (ProjectorVectorSheaf.isSheaf hX M.module.property)

/-- The actual action sheaf reconstructed on the published projector families. -/
def sheaf : SectionActions.ActionSheaf G X :=
  ⟨transportPresheaf hX M, isSheaf hX M⟩

/-- The ordinary vector sheaf is the published one, by identity family maps. -/
def underlyingSheafIso :
    SectionActions.underlying (sheaf hX M) ≅
      ProjectorVectorSheaf.sheaf hX M.module.property where
  hom := ObjectProperty.homMk (underlyingIso hX M).hom
  inv := ObjectProperty.homMk (underlyingIso hX M).inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact (underlyingIso hX M).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact (underlyingIso hX M).inv_hom_id

variable {M} {N : CompatibleTestAction.{uG, 0, 0} G X}

/-- The existing module map acts componentwise and commutes with every labelled pullback. -/
def transportMap (φ : M ⟶ N) : transportPresheaf hX M ⟶ transportPresheaf hX N where
  app U := (ProjectorVectorSheaf.presheafMap hX M.module.property N.module.property
    φ.moduleHom.hom).app (op U.unop.openSet)
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro W
    apply Subtype.ext
    exact φ.comm f.unop.label⁻¹ (s.val (translatedInside hX f.unop W)).val

/-- The original projector sheaf map, now as an equivariant sheaf map. -/
def sheafMap (φ : M ⟶ N) : sheaf hX M ⟶ sheaf hX N :=
  ObjectProperty.homMk (transportMap hX φ)

/-- Reconstruct the actual action sheaf of every compatible nondegenerate test module. -/
def functor : CompatibleTestAction.{uG, 0, 0} G X ⥤ SectionActions.ActionSheaf G X where
  obj M := sheaf hX M
  map φ := sheafMap hX φ
  map_id M := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro W
    rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro W
    rfl

/-- Forgetting group labels recovers the existing vector-sheaf functor naturally. -/
def forgetIso :
    functor (G := G) hX ⋙ toSheaf G X (ModuleCat.{0} ℂ) ≅
      CompatibleTestAction.toTestModule G X ⋙ ProjectorVectorSheaf.functor hX :=
  NatIso.ofComponents (underlyingSheafIso hX) (by
    intro M N φ
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl)

end Langlands.Sheaf.Renard.ProjectorActionSheaf
