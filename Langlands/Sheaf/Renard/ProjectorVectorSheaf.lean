import Langlands.Sheaf.Renard.ProjectorSheafFunctor
import Langlands.Sheaf.Renard.BasisMathlibSheafEquivalence
import Langlands.Algebra.NondegenerateScalars
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Complex vector sheaves of nondegenerate pointwise-test modules

Renard (9 July 2026), II.2.5, proof of the Theorem, printed pp.39–40 / PDF pp.45–46:
the inverse functor `M ↦ (U ↦ χ_U · M)` with restriction `m ↦ χ_U · m`, refined from the
published additive `ProjectorBasisSheaf.nondegenerateFunctor` to complex vector sheaves by
the canonical complex structure `NondegenerateScalars.complexModule`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace Langlands.Sheaf.Renard.ProjectorVectorSheaf

open ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)

section Values

variable {M : Type v} [AddCommGroup M] [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- Renard's canonical complex structure on the original nondegenerate module. -/
abbrev originalModule : Module ℂ M :=
  NondegenerateScalars.complexModule PointwiseTestAlgebra.isIdempotented hM

include hM in
/-- The original test action commutes with the canonical complex scalars. -/
theorem action_smul_comm (c : ℂ) (a : PointwiseTestAlgebra.Carrier X) (m : M) :
    letI := originalModule hM
    a • (c • m) = c • (a • m) :=
  (NondegenerateScalars.action_smul ℂ PointwiseTestAlgebra.isIdempotented hM c a m).trans
    (NondegenerateScalars.smul_action ℂ PointwiseTestAlgebra.isIdempotented hM c a m).symm

/-- Each compact-open projector range is stable under the canonical complex scalars. -/
theorem smul_mem_value (U : CompactOpen hX) (c : ℂ) (s : Value hX M U) :
    letI := originalModule hM
    c • s.val ∈ NonUnitalModuleCorner.fixedPart (idempotent hX U) M := by
  let _ := originalModule hM
  change (test hX U) • (c • s.val) = c • s.val
  rw [action_smul_comm hM]
  exact congrArg (c • ·) (value_fixed hX M s)

/-- The canonical complex structure on the projector range `χ_U · M`. -/
@[instance_reducible]
def valueModule (U : CompactOpen hX) : Module ℂ (Value hX M U) :=
  letI := originalModule hM
  letI : SMul ℂ (Value hX M U) := ⟨fun c s => ⟨c • s.val, smul_mem_value hX hM U c s⟩⟩
  Function.Injective.module ℂ (NonUnitalModuleCorner.inclusion (idempotent hX U))
    Subtype.val_injective (fun _ _ => rfl)

@[simp] theorem valueModule_smul_val (U : CompactOpen hX) (c : ℂ) (s : Value hX M U) :
    (@HSMul.hSMul ℂ (Value hX M U) (Value hX M U)
      (@instHSMul _ _ (valueModule hX hM U).toSMul) c s).val =
      @HSMul.hSMul ℂ M M (@instHSMul _ _ (originalModule hM).toSMul) c s.val := rfl

/-- Projector restriction commutes with the canonical complex scalars. -/
theorem restrict_smul {U V : CompactOpen hX} (h : U.obj ≤ V.obj) (c : ℂ) (s : Value hX M V) :
    restrict hX M h (@HSMul.hSMul ℂ _ _ (@instHSMul _ _ (valueModule hX hM V).toSMul) c s) =
      @HSMul.hSMul ℂ _ _ (@instHSMul _ _ (valueModule hX hM U).toSMul) c (restrict hX M h s) :=
  Subtype.ext (action_smul_comm hM c (test hX U) s.val)

end Values

section Families

variable {M : Type (max u v)} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- Componentwise canonical complex scalars on compatible projector families. -/
def familySMul (V : Opens X) (c : ℂ)
    (s : BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V) :
    BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V :=
  ⟨fun U => @HSMul.hSMul ℂ _ _ (@instHSMul _ _ (valueModule hX hM U.val).toSMul) c (s.val U),
    fun U W h => (restrict_smul hX hM h c (s.val U)).trans
      (congrArg _ (s.property U W h))⟩

@[simp] theorem familySMul_val (V : Opens X) (c : ℂ)
    (s : BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((familySMul hX hM V c s).val U).val =
      @HSMul.hSMul ℂ M M (@instHSMul _ _ (originalModule hM).toSMul) c (s.val U).val := rfl

/-- The complex structure on compatible families, componentwise from the projector ranges. -/
@[instance_reducible]
def familyModule (V : Opens X) :
    Module ℂ (BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V) :=
  letI : SMul ℂ (BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V) := ⟨familySMul hX hM V⟩
  letI : Module ℂ
      (∀ U : BasisAllOpen.Inside (compactOpenBasis hX) V, Sections (rawPresheaf hX M) U.val) :=
    @Pi.module (BasisAllOpen.Inside (compactOpenBasis hX) V)
      (fun U => Sections (rawPresheaf hX M) U.val) ℂ _ _
      (fun U => valueModule hX hM U.val)
  Function.Injective.module ℂ
    (BasisAllOpen.familySubgroup.{u,v} (rawPresheaf hX M) V).subtype
    Subtype.val_injective (fun _ _ => rfl)

/-- The complex vector space of compatible families on an actual open. -/
def familySpace (V : Opens X) : ModuleCat.{max u v} ℂ :=
  @ModuleCat.of ℂ _ (BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V) _
    (familyModule hX hM V)

/-- Discarding components is complex-linear. -/
def familyRestrictionLinear {U V : Opens X} (h : U ≤ V) :
    familySpace hX hM V ⟶ familySpace hX hM U :=
  letI := familyModule hX hM V
  letI := familyModule hX hM U
  ModuleCat.ofHom
    { toFun := BasisAllOpen.familyRestriction (rawPresheaf hX M) h
      map_add' := (BasisAllOpen.familyRestriction (rawPresheaf hX M) h).map_add
      map_smul' := fun _ _ => rfl }

/-- The actual presheaf of complex vector spaces of compatible projector families. -/
def presheaf : TopCat.Presheaf (ModuleCat.{max u v} ℂ) (TopCat.of X) where
  obj V := familySpace hX hM V.unop
  map f := familyRestrictionLinear hX hM f.unop.le
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro U
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro U
    rfl

/-- Forgetting scalars gives exactly the published additive Mathlib sheaf. -/
theorem presheaf_forget₂ :
    presheaf hX hM ⋙ forget₂ (ModuleCat.{max u v} ℂ) AddCommGrpCat.{max u v} =
      ((BasisMathlib.toMathlib.{u,v} (compactOpenBasis hX)).obj (basisSheaf hX M)).obj :=
  rfl

theorem isSheaf : TopCat.Presheaf.IsSheaf (presheaf hX hM) := by
  have := ModuleCat.hasLimitsOfSize.{u, u, max u v, 0} (R := ℂ)
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget₂ (ModuleCat.{max u v} ℂ) AddCommGrpCat.{max u v}), presheaf_forget₂]
  exact ((BasisMathlib.toMathlib.{u,v} (compactOpenBasis hX)).obj (basisSheaf hX M)).property

/-- The actual sheaf of complex vector spaces attached to a nondegenerate module. -/
def sheaf : TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X) :=
  ⟨presheaf hX hM, isSheaf hX hM⟩

/-- On a compact open `U`, the complex sections are exactly the projector range `χ_U · M`;
this refines the published additive `BasisMathlib.basisSectionIso`. -/
def sectionLinearEquiv (U : CompactOpen hX) :
    letI := valueModule hX hM U
    Value hX M U ≃ₗ[ℂ] (presheaf hX hM).obj (op U.obj) :=
  letI := valueModule hX hM U
  { BasisMathlib.basisSectionIso.{u,v} (compactOpenBasis hX) (basisSheaf hX M) U with
    map_smul' := fun c s => by
      apply BasisAllOpen.families_ext
      intro W
      exact restrict_smul hX hM W.property c s }

theorem sectionLinearEquiv_apply (U : CompactOpen hX) (s : Value hX M U)
    (W : BasisAllOpen.Inside (compactOpenBasis hX) U.obj) :
    letI := valueModule hX hM U
    (sectionLinearEquiv hX hM U s).val W = restrict hX M W.property s := rfl

theorem sectionLinearEquiv_symm_apply (U : CompactOpen hX)
    (s : (presheaf hX hM).obj (op U.obj)) :
    letI := valueModule hX hM U
    (sectionLinearEquiv hX hM U).symm s = s.val ⟨U, le_rfl⟩ := rfl

theorem sectionLinearEquiv_toAddEquiv (U : CompactOpen hX) :
    letI := valueModule hX hM U
    (sectionLinearEquiv hX hM U).toAddEquiv =
      BasisMathlib.basisSectionIso.{u,v} (compactOpenBasis hX) (basisSheaf hX M) U := rfl

end Families

section Morphisms

variable {M N P : Type (max u v)} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) P]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)
  (hN : IsNondegenerate (PointwiseTestAlgebra.Carrier X) N)
  (hP : IsNondegenerate (PointwiseTestAlgebra.Carrier X) P)

/-- The published componentwise family map is complex-linear for the canonical scalars. -/
def familyLinearMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (V : Opens X) : familySpace hX hM V ⟶ familySpace hX hN V :=
  letI := familyModule hX hM V
  letI := familyModule hX hN V
  ModuleCat.ofHom
    { toFun := BasisAllOpen.familyMap (rawMap hX f) V
      map_add' := (BasisAllOpen.familyMap (rawMap hX f) V).map_add
      map_smul' := fun c s => by
        apply BasisAllOpen.families_ext
        intro U
        apply Subtype.ext
        exact NondegenerateScalars.map_smul ℂ PointwiseTestAlgebra.isIdempotented hM hN f c
          (s.val U).val }

@[simp] theorem familyLinearMap_val
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) (V : Opens X)
    (s : BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    (((familyLinearMap hX hM hN f V).hom s).val U).val = f (s.val U).val := rfl

/-- The complex-linear natural transformation with original-map components. -/
def presheafMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    presheaf hX hM ⟶ presheaf hX hN where
  app V := familyLinearMap hX hM hN f V.unop
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply BasisAllOpen.families_ext
    intro U
    rfl

/-- The actual morphism of complex vector sheaves induced by an original intertwiner. -/
def sheafMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    sheaf hX hM ⟶ sheaf hX hN :=
  ObjectProperty.homMk (presheafMap hX hM hN f)

@[simp] theorem sheafMap_app_val
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) (V : Opens X)
    (s : BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((((sheafMap hX hM hN f).hom.app (op V)).hom s).val U).val = f (s.val U).val := rfl

theorem sheafMap_id :
    sheafMap hX hM hM (NonUnitalModuleHom.id (PointwiseTestAlgebra.Carrier X) M) =
      𝟙 (sheaf hX hM) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply BasisAllOpen.families_ext
  intro U
  rfl

theorem sheafMap_comp
    (g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) N P)
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    sheafMap hX hM hP (g.comp f) = sheafMap hX hM hN f ≫ sheafMap hX hN hP g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply BasisAllOpen.families_ext
  intro U
  rfl

end Morphisms

/-- Renard's inverse functor from nondegenerate test modules to complex vector sheaves. -/
def functor :
    NondegenerateModuleCat.{u, max u v} (PointwiseTestAlgebra.Carrier X) ⥤
      TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X) where
  obj M := sheaf hX M.property
  map f := sheafMap hX _ _ f.hom
  map_id M := sheafMap_id hX M.property
  map_comp f g := sheafMap_comp hX _ _ _ g.hom f.hom

@[simp] theorem functor_obj
    (M : NondegenerateModuleCat.{u, max u v} (PointwiseTestAlgebra.Carrier X)) :
    (functor hX).obj M = sheaf hX M.property := rfl

@[simp] theorem functor_map
    {M N : NondegenerateModuleCat.{u, max u v} (PointwiseTestAlgebra.Carrier X)}
    (f : M ⟶ N) : (functor hX).map f = sheafMap hX M.property N.property f.hom := rfl

/-- Forgetting the complex structure recovers the published additive construction exactly. -/
theorem functor_comp_forget₂ :
    functor.{u,v} hX ⋙ sheafCompose (Opens.grothendieckTopology (TopCat.of X))
        (forget₂ (ModuleCat.{max u v} ℂ) AddCommGrpCat.{max u v}) =
      nondegenerateFunctor.{u, max u v} hX ⋙
        BasisMathlib.toMathlib.{u,v} (compactOpenBasis hX) :=
  rfl

/-! Complete unapplied interfaces, including the all-`Type` instance used by
`Langlands.Sheaf.CompactSupport`. -/

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{u, max u v} (PointwiseTestAlgebra.Carrier X) ⥤
      TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X) :=
  @functor.{u,v}

example : {X : Type} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X) ⥤
      TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  @functor.{0,0}

example : {X : Type 1} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{1, 2} (PointwiseTestAlgebra.Carrier X) ⥤
      TopCat.Sheaf (ModuleCat.{2} ℂ) (TopCat.of X) :=
  @functor.{1,2}

end Langlands.Sheaf.Renard.ProjectorVectorSheaf
