import Langlands.Sheaf.Renard.HomogeneousSections
import Langlands.Sheaf.Renard.CompatibleTestActions
import Langlands.Representation.Induction.CompactLocallyConstant

/-!
# Pointwise test modules on actual compact induction

Multiplication retains the published compact-induced functions. Local constancy
and compact projected support supply their uniform open right stabilizers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.CompactInductionTestModule

open CategoryTheory
open Langlands.Induction Langlands.Algebra
open Langlands.HarmonicAnalysis.PointwiseTestAlgebra
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.HomogeneousSections

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (σ : Representation ℂ H V)

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
private theorem quotientMap_subgroup_mul (h : H) (g : G) :
    quotientMap H ((h : G) * g) = quotientMap H g := by
  apply Quotient.sound
  change QuotientGroup.rightRel H ((h : G) * g) g
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev]

/-- Scalar multiplication of the original covariant function by a quotient scalar. -/
def productFunction (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) (g : G) : V :=
  φ (quotientMap H g) • eval H σ f.val g

omit [LocallyCompactSpace G] in
/-- Quotient scalars preserve the original left covariance. -/
theorem productFunction_covariant (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) (h : H) (g : G) :
    productFunction H σ φ f ((h : G) * g) =
      σ h (productFunction H σ φ f g) := by
  simp only [productFunction, quotientMap_subgroup_mul, eval_covariant, map_smul]

omit [LocallyCompactSpace G] in
/-- Multiplication retains pointwise local constancy. -/
theorem productFunction_locallyConstant (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) : IsLocallyConstant (productFunction H σ φ f) :=
  (φ.isLocallyConstant.comp_continuous continuous_quotient_mk').comp₂
    (eval_isLocallyConstant H σ f.val) (fun c v => c • v)

omit [LocallyCompactSpace G] in
/-- Covariance and local constancy make the product's projected support closed. -/
theorem productFunction_support_closed (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) :
    IsClosed (quotientSupport H (productFunction H σ φ f)) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isClosed_preimage.mp
  have heq : quotientMap H ⁻¹' quotientSupport H (productFunction H σ φ f) =
      Function.support (productFunction H σ φ f) := by
    ext g
    exact quotientMap_mem_quotientSupport_iff_of_covariant H σ _
      (productFunction_covariant H σ φ f) g
  change IsClosed (quotientMap H ⁻¹' quotientSupport H (productFunction H σ φ f))
  rw [heq]
  exact (productFunction_locallyConstant H σ φ f).isOpen_fiber 0 |>.isClosed_compl

omit [LocallyCompactSpace G] in
/-- Multiplication cannot enlarge the original compact projected support. -/
theorem productFunction_support_subset (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) :
    quotientSupport H (productFunction H σ φ f) ⊆
      quotientSupport H (eval H σ f.val) := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  intro hf
  exact hg (by simp [productFunction, hf])

/-- Multiplication by an arbitrary locally constant quotient scalar on actual compact induction. -/
def multiplier (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) : CompactFunctions H σ :=
  compactFunctionOfLocallyConstant H hH σ (productFunction H σ φ f)
    (productFunction_covariant H σ φ f)
    (productFunction_locallyConstant H σ φ f)
    (f.property.of_isClosed_subset (productFunction_support_closed H σ φ f)
      (productFunction_support_subset H σ φ f))

@[simp]
theorem multiplier_apply (φ : LocallyConstant (LeftQuotient H) ℂ)
    (f : CompactFunctions H σ) (g : G) :
    eval H σ (multiplier H hH σ φ f).val g =
      φ (quotientMap H g) • eval H σ f.val g := rfl

omit [LocallyCompactSpace G] in
private theorem compact_ext {f k : CompactFunctions H σ}
    (h : ∀ g, eval H σ f.val g = eval H σ k.val g) : f = k := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact funext h

/-- The original compact-induced carrier as a module over the original pointwise tests. -/
@[instance_reducible]
def testModule : NonUnitalModule (Carrier (LeftQuotient H)) (CompactFunctions H σ) where
  smul φ f := multiplier H hH σ φ.val f
  smul_zero φ := by
    apply compact_ext H σ
    intro g
    change φ (quotientMap H g) • (0 : V) = 0
    exact smul_zero _
  smul_add φ f k := by
    apply compact_ext H σ
    intro g
    change φ (quotientMap H g) • (eval H σ f.val g + eval H σ k.val g) = _
    exact smul_add _ _ _
  mul_smul φ ψ f := by
    apply compact_ext H σ
    intro g
    change (φ (quotientMap H g) * ψ (quotientMap H g)) • eval H σ f.val g =
      φ (quotientMap H g) • (ψ (quotientMap H g) • eval H σ f.val g)
    exact mul_smul _ _ _
  add_smul φ ψ f := by
    apply compact_ext H σ
    intro g
    change (φ (quotientMap H g) + ψ (quotientMap H g)) • eval H σ f.val g = _
    exact add_smul _ _ _
  zero_smul f := by
    apply compact_ext H σ
    intro g
    change (0 : ℂ) • eval H σ f.val g = 0
    exact zero_smul _ _

/-- The same complex scalar multiplication already used by the original induction model. -/
theorem testModule_scalarTower :
    letI := testModule H hH σ
    IsScalarTower ℂ (Carrier (LeftQuotient H)) (CompactFunctions H σ) := by
  let := testModule H hH σ
  refine ⟨fun c φ f => ?_⟩
  apply compact_ext H σ
  intro g
  change (c • φ) (quotientMap H g) • eval H σ f.val g =
    c • (φ (quotientMap H g) • eval H σ f.val g)
  exact smul_assoc c (φ (quotientMap H g)) _

omit [LocallyCompactSpace G] in
/-- The projected support of a smooth covariant function is also open. -/
theorem quotientSupport_isOpen (f : CompactFunctions H σ) :
    IsOpen (quotientSupport H (eval H σ f.val)) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
  change IsOpen (quotientMap H ⁻¹' quotientSupport H (eval H σ f.val))
  rw [quotientMap_preimage_quotientSupport]
  exact (eval_isLocallyConstant H σ f.val).isClosed_fiber 0 |>.isOpen_compl

/-- Its own compact-clopen support gives an actual characteristic idempotent fixer. -/
theorem testModule_nondegenerate :
    letI := testModule H hH σ
    IsNondegenerate (Carrier (LeftQuotient H)) (CompactFunctions H σ) := by
  let := testModule H hH σ
  intro f
  let e := characteristicIdempotent
    ⟨isClosed_quotientSupport H σ f.val, quotientSupport_isOpen H σ f⟩ f.property
  refine ⟨e, ?_⟩
  apply compact_ext H σ
  intro g
  change characteristic _ _ (quotientMap H g) • eval H σ f.val g = eval H σ f.val g
  by_cases hf : eval H σ f.val g = 0
  · simp [hf]
  · have hg : quotientMap H g ∈ quotientSupport H (eval H σ f.val) := ⟨g, hf, rfl⟩
    simp only [characteristic_apply, Set.indicator_of_mem hg, one_smul]

/-- The object of the published nondegenerate test-module category, on the original carrier. -/
def moduleObject : NondegenerateModuleCat.{uG, max uG uV} (Carrier (LeftQuotient H)) :=
  letI := testModule H hH σ
  ⟨NonUnitalModuleCat.of (Carrier (LeftQuotient H)) (CompactFunctions H σ),
    testModule_nondegenerate H hH σ⟩

/-- The reconstructed complex scalars agree with the original induced-space scalars. -/
theorem canonicalComplexModule :
    letI := testModule H hH σ
    NondegenerateScalars.module ℂ isIdempotented (testModule_nondegenerate H hH σ) =
      (inferInstance : Module ℂ (CompactFunctions H σ)) := by
  let := testModule H hH σ
  let := testModule_scalarTower H hH σ
  exact NondegenerateScalars.module_eq_of_compatible ℂ isIdempotented
    (testModule_nondegenerate H hH σ)

attribute [local instance] homogeneousAction

/-- The pointwise action has the source's compatibility with inverse pullback on tests. -/
theorem action_compatible (g : G) (φ : Carrier (LeftQuotient H))
    (f : CompactFunctions H σ) :
    letI := testModule H hH σ
    compactInduced H σ g (φ • f) =
      testRepresentation g φ • compactInduced H σ g f := by
  let := testModule H hH σ
  apply compact_ext H σ
  intro k
  change φ (quotientMap H (k * g)) • eval H σ f.val (k * g) =
    testRepresentation g φ (quotientMap H k) • eval H σ f.val (k * g)
  rw [testRepresentation_apply, smul_quotientMap, inv_inv]

/-- Pointwise comparison of the canonical complex action and the original scalar action. -/
theorem canonicalScalar_eq (c : ℂ) (f : CompactFunctions H σ) :
    letI := testModule H hH σ
    NondegenerateScalars.scalarMul ℂ (testModule_nondegenerate H hH σ) c f = c • f := by
  let := testModule H hH σ
  let := testModule_scalarTower H hH σ
  exact NondegenerateScalars.scalarMul_eq_of_compatible ℂ
    (testModule_nondegenerate H hH σ) c f

/-- The original right translations are linear for the canonical recovered scalars. -/
def canonicalAction :
    letI := NondegenerateScalars.module ℂ isIdempotented (moduleObject H hH σ).property
    Representation ℂ G (moduleObject H hH σ).obj := by
  letI := testModule H hH σ
  letI := NondegenerateScalars.module ℂ isIdempotented (moduleObject H hH σ).property
  refine
    { toFun := fun g =>
        { toFun := fun f => compactInduced H σ g f
          map_add' := fun f k => map_add (compactInduced H σ g) f k
          map_smul' := fun c f => ?_ }
      map_one' := ?_
      map_mul' := fun g k => ?_ }
  · change compactInduced H σ _
        (NondegenerateScalars.scalarMul ℂ (testModule_nondegenerate H hH σ) c f) =
      NondegenerateScalars.scalarMul ℂ (testModule_nondegenerate H hH σ) c
        (compactInduced H σ _ f)
    rw [canonicalScalar_eq, canonicalScalar_eq, map_smul]
  · ext f
    change compactInduced H σ 1 f = f
    simp
  · ext f
    change compactInduced H σ (g * k) f =
      compactInduced H σ g (compactInduced H σ k f)
    exact LinearMap.congr_fun (map_mul (compactInduced H σ) g k) f

/-- Actual compact induction, bundled in the published compatible-action category. -/
def compatibleObject : CompatibleTestAction.{uG, uG, max uG uV} G (LeftQuotient H) where
  module := moduleObject H hH σ
  action := canonicalAction H hH σ
  compatible := action_compatible H hH σ

variable {W : Type uV} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W}

/-- The original induced map is linear for the original pointwise test action. -/
def moduleMap (T : σ.IntertwiningMap τ) :
    moduleObject H hH σ ⟶ moduleObject H hH τ :=
  ObjectProperty.homMk
    { toAddMonoidHom := (compactInducedMap H T).toLinearMap.toAddMonoidHom
      map_smul' φ f := by
        apply compact_ext H τ
        intro g
        change T (φ (quotientMap H g) • eval H σ f.val g) =
          φ (quotientMap H g) • T (eval H σ f.val g)
        exact map_smul T _ _ }

/-- The original induced map also commutes with the original right translations. -/
def compatibleMap (T : σ.IntertwiningMap τ) :
    compatibleObject H hH σ ⟶ compatibleObject H hH τ where
  moduleHom := moduleMap H hH σ T
  comm g f := LinearMap.congr_fun ((compactInducedMap H T).isIntertwining' g) f

variable (G)

/-- Compact induction with its pointwise tests, on the original objects and maps. -/
def functor : Rep.{uV} ℂ H ⥤
    CompatibleTestAction.{uG, uG, max uG uV} G (LeftQuotient H) where
  obj A := compatibleObject H hH A.ρ
  map f := compatibleMap H hH _ f.hom
  map_id A := by
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro f
    apply compact_ext H A.ρ
    intro g
    rfl
  map_comp {A B C} f k := by
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    apply compact_ext H C.ρ
    intro g
    rfl

end Langlands.Sheaf.Renard.CompactInductionTestModule
