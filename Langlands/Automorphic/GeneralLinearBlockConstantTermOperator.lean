import Langlands.Automorphic.GeneralLinearBlockConstantTermTransitivity
import Langlands.Automorphic.GroupSchemeFiniteLevel
import Langlands.Global.RankinSelberg.WhittakerCurveDerivative

/-! # Operator stability of the block constant-term kernels of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology Metric
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL
  Langlands.Global.AdelicSubgroupPoints Langlands.Global.GeneralLinearBlockSemidirect
  Global.RankinSelbergGlobal.WhittakerCurve

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "N(" e ")" => GroupScheme.GeneralLinear.blockUnipotent (Fin n) RF e

local instance blockConstantTermOperatorAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) RF

local instance blockConstantTermOperatorSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) RF

local instance blockConstantTermOperatorClosed (e : Fin n → ℤ) :
    IsClosed (adelicPoints F GLG N(e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance blockConstantTermOperatorCompact (e : Fin n → ℤ) :
    CompactSpace (RationalQuotient F GLG N(e)) :=
  GroupSchemeFunctions.blockUnipotentRationalQuotientCompactSpace F e

local instance blockConstantTermOperatorBorel (e : Fin n → ℤ) :
    BorelSpace (RationalQuotient F GLG N(e)) :=
  rationalQuotientBorelSpace F GLG N(e)

local instance blockConstantTermOperatorProbability (e : Fin n → ℤ) :
    IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F GLG N(e)) :=
  normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F GLG N(e)

local instance blockConstantTermOperatorRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _

local instance blockConstantTermOperatorContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _

local instance blockConstantTermOperatorFiniteSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

private theorem constantTerm_hasDerivAt
    {G : GroupScheme (Spec RF)} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (U : GroupScheme.SubgroupFunctor G) [CompactSpace (RationalQuotient F G U)]
    [BorelSpace (RationalQuotient F G U)]
    (ν : Measure (RationalQuotient F G U)) [IsFiniteMeasure ν]
    (f df : GroupSchemeFunctions.ContinuousRationalFunctions F G)
    (curve : ℝ → AdelicGroupPoints F G) (hcurve : Continuous curve)
    (hd : ∀ (z : adelicPoints F G U) s, HasDerivAt
      (fun t => GroupSchemeFunctions.evaluate F G f (z.val * curve t))
      (GroupSchemeFunctions.evaluate F G df (z.val * curve s)) s) (t : ℝ) :
    HasDerivAt (fun s => GroupSchemeFunctions.constantTerm F G U ν f (curve s))
      (GroupSchemeFunctions.constantTerm F G U ν df (curve t)) t := by
  let Γ := rationalSubgroup F G U
  let integrand (a : GroupSchemeFunctions.ContinuousRationalFunctions F G) (s : ℝ) :=
    GroupSchemeFunctions.constantTermIntegrand F G U a (curve s)
  have hc : Continuous (Function.uncurry (integrand df)) := by
    have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (LeftCosetSpace.mk Γ)) :=
      IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
    apply hq.isQuotientMap.continuous_iff.mpr
    change Continuous (fun p : ℝ × adelicPoints F G U =>
      GroupSchemeFunctions.evaluate F G df (p.2.val * curve p.1))
    exact df.property.comp ((continuous_subtype_val.comp continuous_snd).mul
      (hcurve.comp continuous_fst))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set (RationalQuotient F G U)))).exists_bound_of_continuousOn
      hc.continuousOn
  have hcont (a : GroupSchemeFunctions.ContinuousRationalFunctions F G) (s : ℝ) :
      Continuous (integrand a s) :=
    GroupSchemeFunctions.continuous_constantTermIntegrand F G U a (curve s)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℂ)
    («μ» := ν) (F := integrand f) (F' := integrand df) (x₀ := t) (bound := fun _ => C)
    (closedBall_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hcont f s).aestronglyMeasurable
  · exact (hcont f t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hcont df t).aestronglyMeasurable
  · exact ae_of_all _ fun q s hs => hC (s, q) ⟨hs, Set.mem_univ _⟩
  · exact integrable_const C
  · refine ae_of_all _ fun q s _ => ?_
    obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    exact hd z s

private def schemeContinuousFunction :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] GroupSchemeFunctions.ContinuousRationalFunctions F GLG :=
  (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm.toLinearMap ∘ₗ
    (finiteSmoothRationalSubrepresentation F n).toSubmodule.subtype

/-- The mass-one block constant term is a linear map on the original finite-smooth
rational-invariant function space. -/
def finiteSmoothBlockConstantTerm (e : Fin n → ℤ) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) :=
  GroupSchemeFunctions.compactConstantTermLinearMap F GLG N(e)
      (normalizedRationalQuotientHaarMeasure F GLG N(e)) ∘ₗ
    schemeContinuousFunction F

theorem finiteSmoothBlockConstantTerm_apply (e : Fin n → ℤ) (f : FiniteSmoothRationalFunctions F n)
    (g : AdelicGroupPoints F GLG) :
    finiteSmoothBlockConstantTerm F e f g =
      GroupSchemeFunctions.normalizedBlockConstantTerm F e
        ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val) g := rfl

theorem finiteSmoothBlockConstantTerm_rightAction (e : Fin n → ℤ)
    (f : FiniteSmoothRationalFunctions F n) (h g : AdelicGroupPoints F GLG) :
    finiteSmoothBlockConstantTerm F e
        (finiteSmoothRightAction F n (GeneralLinearGroupPoints.adelicEquiv F n h) f) g =
      finiteSmoothBlockConstantTerm F e f (g * h) := by
  have hcomp : schemeContinuousFunction F
        (finiteSmoothRightAction F n (GeneralLinearGroupPoints.adelicEquiv F n h) f) =
      GroupSchemeFunctions.continuousRightAction F GLG h (schemeContinuousFunction F f) := by
    apply (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).injective
    rw [GroupSchemeFunctions.continuousGeneralLinearEquiv_rightAction]
    simp only [schemeContinuousFunction, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, LinearEquiv.apply_symm_apply]
    rfl
  change GroupSchemeFunctions.constantTerm F GLG N(e) _ (schemeContinuousFunction F
    (finiteSmoothRightAction F n (GeneralLinearGroupPoints.adelicEquiv F n h) f)) g =
      GroupSchemeFunctions.constantTerm F GLG N(e) _ (schemeContinuousFunction F f) (g * h)
  rw [hcomp, GroupSchemeFunctions.constantTerm_rightAction]

private theorem finiteSmooth_hasDerivAt_oneParameter
    (X : RealLieAlgebra F n) (f : FiniteSmoothRationalFunctions F n)
    (g : AdelicGroupPoints F GLG) (t : ℝ) :
    HasDerivAt (fun s => GroupSchemeFunctions.evaluate F GLG (schemeContinuousFunction F f)
      (g * adelicOneParameter F n X s))
      (GroupSchemeFunctions.evaluate F GLG (schemeContinuousFunction F
        (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f))
        (g * adelicOneParameter F n X t)) t := by
  let x := GeneralLinearGroupPoints.adelicEquiv F n g
  have h := hasDerivAt_smooth_oneParameter F n
    (finiteSmoothSlice F n (AdelicGL.finite F n x) f) X (AdelicGL.infinite F n x) t
  simp only [finiteSmoothSlice_apply] at h
  change HasDerivAt (fun s => ContinuousRationalFunctions.evaluate F n f.val
      (GeneralLinearGroupPoints.adelicEquiv F n (g * adelicOneParameter F n X s)))
      (ContinuousRationalFunctions.evaluate F n
        (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f).val
        (GeneralLinearGroupPoints.adelicEquiv F n (g * adelicOneParameter F n X t))) t
  simp only [map_mul, adelicOneParameter, MulEquiv.apply_symm_apply,
    OperatorRealization.mul_ofInfinite_eq_pair, evaluate_finiteSmoothEnvelopingAction,
    envelopingAction_real_generator]
  exact h

/-- Differentiating a block constant term along a real right Lie curve gives the
block constant term of the corresponding derivative of the original function. -/
theorem finiteSmoothBlockConstantTerm_hasDerivAt (e : Fin n → ℤ)
    (X : RealLieAlgebra F n) (f : FiniteSmoothRationalFunctions F n)
    (g : AdelicGroupPoints F GLG) (t : ℝ) :
    HasDerivAt (fun s => finiteSmoothBlockConstantTerm F e f (g * adelicOneParameter F n X s))
      (finiteSmoothBlockConstantTerm F e
        (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f)
        (g * adelicOneParameter F n X t)) t := by
  refine constantTerm_hasDerivAt F N(e) (normalizedRationalQuotientHaarMeasure F GLG N(e))
    (schemeContinuousFunction F f)
    (schemeContinuousFunction F
      (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f))
    (fun s => g * adelicOneParameter F n X s)
    (continuous_const.mul (continuous_adelicOneParameter F n X)) ?_ t
  intro z s
  simpa only [mul_assoc] using finiteSmooth_hasDerivAt_oneParameter F X f (z.val * g) s

private theorem realGenerator_mem_blockConstantTermKernel (e : Fin n → ℤ)
    (X : RealLieAlgebra F n) {f : FiniteSmoothRationalFunctions F n}
    (hf : f ∈ (finiteSmoothBlockConstantTerm F e).ker) :
    finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f ∈
      (finiteSmoothBlockConstantTerm F e).ker := by
  apply LinearMap.mem_ker.mpr
  funext g
  have hz : (fun s => finiteSmoothBlockConstantTerm F e f (g * adelicOneParameter F n X s)) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext s
    exact congrFun (LinearMap.mem_ker.mp hf) _
  have h := finiteSmoothBlockConstantTerm_hasDerivAt F e X f g 0
  rw [hz] at h
  simpa only [adelicOneParameter, infiniteOneParameter_zero, map_one, mul_one, Pi.zero_apply] using
    h.unique (hasDerivAt_const 0 (0 : ℂ))

private theorem enveloping_mem_blockConstantTermKernel (e : Fin n → ℤ)
    (a : EnvelopingAlgebra F n) (f : FiniteSmoothRationalFunctions F n)
    (hf : f ∈ (finiteSmoothBlockConstantTerm F e).ker) :
    finiteSmoothEnvelopingAction F n a f ∈ (finiteSmoothBlockConstantTerm F e).ker := by
  let P := (finiteSmoothBlockConstantTerm F e).ker
  let A := finiteSmoothEnvelopingAction F n
  suffices ∀ f ∈ P, A a f ∈ P by exact this f hf
  have hgen (X : ComplexLieAlgebra F n) : ∀ f ∈ P, A (envelopingGenerator F n X) f ∈ P := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      intro y hy
      have hx : c ⊗ₜ[ℝ] X = c • complexify F n X := by
        simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hx, map_smul, map_smul, LinearMap.smul_apply]
      exact P.smul_mem c (realGenerator_mem_blockConstantTermKernel F e X hy)
    | add X Y hX hY =>
      intro y hy
      rw [map_add, map_add, LinearMap.add_apply]
      exact P.add_mem (hX y hy) (hY y hy)
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra F n)
  change ∀ f ∈ P, A (q t) f ∈ P
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    intro y hy
    rw [q.commutes, A.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    exact P.smul_mem c hy
  | «ι» X => exact hgen X
  | mul a b ha hb =>
    intro y hy
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha _ (hb y hy)
  | add a b ha hb =>
    intro y hy
    rw [map_add, map_add, LinearMap.add_apply]
    exact P.add_mem (ha y hy) (hb y hy)

/-- The kernel of each actual normalized block constant term is a subrepresentation
for the concrete finite, compact and enveloping operator algebra. -/
def blockConstantTermKernel (e : Fin n → ℤ) : Subrepresentation (automorphicOperatorAction F n) where
  toSubmodule := (finiteSmoothBlockConstantTerm F e).ker
  apply_mem_toSubmodule := (operator_invariant_iff F n _).mpr
    ⟨fun d f hf => by
        apply LinearMap.mem_ker.mpr
        funext g
        obtain ⟨h, hh⟩ := (GeneralLinearGroupPoints.adelicEquiv F n).surjective
          (AdelicGL.ofFinite F n d)
        change finiteSmoothBlockConstantTerm F e
          (finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) f) g = 0
        rw [← hh]
        exact (finiteSmoothBlockConstantTerm_rightAction F e f h g).trans
          (congrFun (LinearMap.mem_ker.mp hf) _),
      fun k f hf => by
        apply LinearMap.mem_ker.mpr
        funext g
        obtain ⟨h, hh⟩ := (GeneralLinearGroupPoints.adelicEquiv F n).surjective
          (AdelicGL.ofInfinite F n k.val)
        change finiteSmoothBlockConstantTerm F e
          (finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) f) g = 0
        rw [← hh]
        exact (finiteSmoothBlockConstantTerm_rightAction F e f h g).trans
          (congrFun (LinearMap.mem_ker.mp hf) _),
      enveloping_mem_blockConstantTermKernel F e⟩

theorem mem_blockConstantTermKernel (e : Fin n → ℤ) (f : FiniteSmoothRationalFunctions F n) :
    f ∈ blockConstantTermKernel F e ↔ ∀ g, finiteSmoothBlockConstantTerm F e f g = 0 := by
  change finiteSmoothBlockConstantTerm F e f = 0 ↔ _
  exact ⟨fun h g => congrFun h g, fun h => funext h⟩

end Langlands.Automorphic
