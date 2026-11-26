import Langlands.Global.AdelicParabolicConstantTermAutomorphy
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicParabolicConstantTermGrowth
import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Automorphic.GroupSchemeEnvelopingAction

/-! # The enveloping action on unipotent constant terms -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions

section Unipotent

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
local notation "m" => map F U G j
local notation "CT" => subgroupConstantTerm F j
local notation "S∞" => InfinitePlotSmoothFunctions F G

/-- The unipotent constant-term integrand of a continuous function left invariant under
`U(F)` is integrable for the normalized quotient measure. -/
theorem integrable_subgroupConstantTermIntegrand_of_unipotentInvariant
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {f : A → ℂ} (hf : Continuous f)
    (hfR : ∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) (g : A) :
    letI : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    Integrable (fun z : Q => f ((Quotient.out z : H).val * g)) ν := by
  let : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hU hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let J : Q → ℂ := LeftCosetSpace.lift Γ (fun y : H => f (y.val * g)) (fun r y => by
    obtain ⟨q, hq⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
    change m (rational F U q) = r.val.val at hq
    change f ((r.val.val * y.val) * g) = _
    rw [← hq, mul_assoc, hfR q])
  have hJ : Continuous J :=
    (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
  have heq : (fun z : Q => f ((Quotient.out z : H).val * g)) = J :=
    funext fun z => congrArg J (Quotient.out_eq z)
  rw [heq]
  exact hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The unipotent constant term is additive on continuous functions left invariant
under `U(F)`. -/
theorem subgroupConstantTerm_add_of_unipotentInvariant
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {f₁ f₂ : A → ℂ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hR₁ : ∀ (q : RationalGroupPoints F U) x, f₁ (m (rational F U q) * x) = f₁ x)
    (hR₂ : ∀ (q : RationalGroupPoints F U) x, f₂ (m (rational F U q) * x) = f₂ x) :
    CT (f₁ + f₂) = CT f₁ + CT f₂ := by
  funext g
  unfold subgroupConstantTerm
  simpa only [Pi.add_apply] using integral_add
    (integrable_subgroupConstantTermIntegrand_of_unipotentInvariant j hU hconn hu hf₁ hR₁ g)
    (integrable_subgroupConstantTermIntegrand_of_unipotentInvariant j hU hconn hu hf₂ hR₂ g)

variable (Lv : Subgroup (FiniteAdelicGroupPoints F G))

/-- Continuous functions on `G(𝔸)` with smooth infinite slices that are left invariant under
`U(F)` and right invariant under the finite-adelic subgroup `Lv`: the functions to which the
archimedean differentiation of the unipotent constant term applies. -/
def IsSmoothUnipotentInvariant (f : A → ℂ) : Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  Continuous f ∧ (∀ b : Gf, ContMDiff I∞ IC ∞ (fun y : G∞ => f (pair F G y b))) ∧
    (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) ∧
    (∀ l ∈ Lv, ∀ x, f (x * ofFinite F G l) = f x)

variable {j hG Lv}

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsSmoothUnipotentInvariant.add {f₁ f₂ : A → ℂ}
    (h₁ : IsSmoothUnipotentInvariant j hG Lv f₁) (h₂ : IsSmoothUnipotentInvariant j hG Lv f₂) :
    IsSmoothUnipotentInvariant j hG Lv (f₁ + f₂) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  refine ⟨h₁.1.add h₂.1, fun b => (h₁.2.1 b).add (h₂.2.1 b), fun q x => ?_, fun l hl x => ?_⟩
  · simp only [Pi.add_apply, h₁.2.2.1 q x, h₂.2.2.1 q x]
  · simp only [Pi.add_apply, h₁.2.2.2 l hl x, h₂.2.2.2 l hl x]

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsSmoothUnipotentInvariant.smul (c : ℂ) {f : A → ℂ}
    (h : IsSmoothUnipotentInvariant j hG Lv f) : IsSmoothUnipotentInvariant j hG Lv (c • f) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  refine ⟨h.1.const_smul c, fun b => ?_, fun q x => ?_, fun l hl x => ?_⟩
  · exact (((ContinuousLinearMap.mul ℝ ℂ) c).contDiff.contMDiff).comp (h.2.1 b)
  · simp only [Pi.smul_apply, h.2.2.1 q x]
  · simp only [Pi.smul_apply, h.2.2.2 l hl x]

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsSmoothUnipotentInvariant.slice_mem {f : A → ℂ}
    (h : IsSmoothUnipotentInvariant j hG Lv f) (b : Gf) :
    functionInfiniteSlice F G f b ∈ S∞ :=
  (isPlotSmooth_iff_contMDiff F G hG _).mpr (h.2.1 b)

variable (j hG Lv)

/-- `u` acts on the slices of every function `f` of the class, and on the slices of its
unipotent constant term, through one function `g` of the class and its constant term. -/
private def EnvelopingRealized (hcalc : AdelicDifferentialCommutator F G hG)
    (u : AdelicEnvelopingAlgebra F G hG) : Prop :=
  ∀ f, IsSmoothUnipotentInvariant j hG Lv f → ∃ g, IsSmoothUnipotentInvariant j hG Lv g ∧
    ∀ b : Gf,
      (∀ h : functionInfiniteSlice F G f b ∈ S∞,
        (plotSmoothEnvelopingAction F G hG hcalc u ⟨_, h⟩).val = functionInfiniteSlice F G g b) ∧
      (∀ h : functionInfiniteSlice F G (CT f) b ∈ S∞,
        (plotSmoothEnvelopingAction F G hG hcalc u ⟨_, h⟩).val =
          functionInfiniteSlice F G (CT g) b)

variable {j hG Lv}

private theorem envelopingRealized_add
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hcalc : AdelicDifferentialCommutator F G hG) {x y : AdelicEnvelopingAlgebra F G hG}
    (hx : EnvelopingRealized j hG Lv hcalc x) (hy : EnvelopingRealized j hG Lv hcalc y) :
    EnvelopingRealized j hG Lv hcalc (x + y) := by
  intro f hf
  obtain ⟨g₁, hg₁, h₁⟩ := hx f hf
  obtain ⟨g₂, hg₂, h₂⟩ := hy f hf
  refine ⟨g₁ + g₂, hg₁.add hg₂, fun b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [map_add, LinearMap.add_apply, Submodule.coe_add, (h₁ b).1 h, (h₂ b).1 h]
    rfl
  · rw [map_add, LinearMap.add_apply, Submodule.coe_add, (h₁ b).2 h, (h₂ b).2 h,
      subgroupConstantTerm_add_of_unipotentInvariant j hU hconn hu hg₁.1 hg₂.1 hg₁.2.2.1
        hg₂.2.2.1]
    rfl

private theorem envelopingRealized_mul
    (hcalc : AdelicDifferentialCommutator F G hG) {x y : AdelicEnvelopingAlgebra F G hG}
    (hx : EnvelopingRealized j hG Lv hcalc x) (hy : EnvelopingRealized j hG Lv hcalc y) :
    EnvelopingRealized j hG Lv hcalc (x * y) := by
  intro f hf
  obtain ⟨g₁, hg₁, h₁⟩ := hy f hf
  obtain ⟨g₂, hg₂, h₂⟩ := hx g₁ hg₁
  refine ⟨g₂, hg₂, fun b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [map_mul, Module.End.mul_apply]
    have e : plotSmoothEnvelopingAction F G hG hcalc y ⟨_, h⟩ = ⟨_, hg₁.slice_mem b⟩ :=
      Subtype.ext ((h₁ b).1 h)
    rw [e]
    exact (h₂ b).1 _
  · rw [map_mul, Module.End.mul_apply]
    have hv := (h₁ b).2 h
    have hmem : functionInfiniteSlice F G (CT g₁) b ∈ S∞ :=
      hv ▸ (plotSmoothEnvelopingAction F G hG hcalc y ⟨_, h⟩).property
    have e : plotSmoothEnvelopingAction F G hG hcalc y ⟨_, h⟩ = ⟨_, hmem⟩ := Subtype.ext hv
    rw [e]
    exact (h₂ b).2 _

private theorem envelopingRealized_algebraMap (hcalc : AdelicDifferentialCommutator F G hG)
    (c : ℂ) :
    EnvelopingRealized j hG Lv hcalc (algebraMap ℂ (AdelicEnvelopingAlgebra F G hG) c) := by
  intro f hf
  refine ⟨c • f, hf.smul c, fun b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [AlgHom.commutes, Module.algebraMap_end_apply]
    rfl
  · rw [AlgHom.commutes, Module.algebraMap_end_apply, subgroupConstantTerm_smul]
    rfl

private theorem envelopingRealized_generator
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hL : IsOpen (Lv : Set Gf)) (hcalc : AdelicDifferentialCommutator F G hG) (c : ℂ)
    (X : W) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothLieGroup F G hG
    letI : LieGroup I∞ (minSmoothness ℝ 3) G∞ := LieGroup.of_le (n := ∞) (by simp)
    EnvelopingRealized j hG Lv hcalc (UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra I∞ G∞) (c ⊗ₜ[ℝ] X)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup I∞ (minSmoothness ℝ 3) G∞ := LieGroup.of_le (n := ∞) (by simp)
  intro f hf
  have hd := adelicUnipotentConstantTermDifferentiation j hG hU hconn hu Lv hL f hf.1 hf.2.1
    hf.2.2.1 hf.2.2.2
  refine ⟨c • adelicDirectionalValue hG X f, (show IsSmoothUnipotentInvariant j hG Lv
    (adelicDirectionalValue hG X f) from hd.1 X).smul c, fun b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul]
    funext a
    change c * mvfderiv I∞ (fun y => f (pair F G (a * y) b)) 1 X =
      c * adelicDirectionalValue hG X f (pair F G a b)
    rw [adelicDirectionalValue_pair]
    rfl
  · rw [plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul,
      subgroupConstantTerm_smul]
    funext a
    change c * groupDirectionalValue I∞ X (fun y => CT f (pair F G y b)) a =
      c * CT (adelicDirectionalValue hG X f) (pair F G a b)
    rw [((hd.2 b).2 X a)]

/-- Every element of the complex enveloping algebra of `G(F_∞)` acts on the infinite slices
of a function of the class through a function of the class, and acts on the slices of the
unipotent constant term through the constant term of that function. -/
private theorem envelopingRealized
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hL : IsOpen (Lv : Set Gf)) (hcalc : AdelicDifferentialCommutator F G hG)
    (z : AdelicEnvelopingAlgebra F G hG) : EnvelopingRealized j hG Lv hcalc z := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup I∞ (minSmoothness ℝ 3) G∞ := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] GroupLieAlgebra I∞ G∞)) z
  change EnvelopingRealized j hG Lv hcalc (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes]
    exact envelopingRealized_algebraMap hcalc c
  | «ι» Z =>
    change EnvelopingRealized j hG Lv hcalc (UniversalEnvelopingAlgebra.ι ℂ Z)
    induction Z using TensorProduct.inductionOn with
    | tmul c X => exact envelopingRealized_generator hU hconn hu hL hcalc c X
    | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add]
      exact envelopingRealized_add hU hconn hu hcalc h₁ h₂
  | mul x y hx hy =>
    rw [map_mul]
    exact envelopingRealized_mul hcalc hx hy
  | add x y hx hy =>
    rw [map_add]
    exact envelopingRealized_add hU hconn hu hcalc hx hy

/-- Finiteness under the center of the enveloping algebra passes to the unipotent constant
term, with the same ideal of finite codimension. -/
theorem isCenterFiniteFunction_subgroupConstantTerm
    (hU : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hL : IsOpen (Lv : Set Gf)) (hcalc : AdelicDifferentialCommutator F G hG) {f : A → ℂ}
    (hf : IsSmoothUnipotentInvariant j hG Lv f) (hZ : IsCenterFiniteFunction F G hG hcalc f) :
    IsCenterFiniteFunction F G hG hcalc (CT f) := by
  obtain ⟨J, hJfin, hJ⟩ := hZ
  refine ⟨J, hJfin, fun z hz b h => ?_⟩
  obtain ⟨g, -, hgs⟩ := envelopingRealized hU hconn hu hL hcalc z.val f hf
  have hg0 : g = 0 := by
    funext x
    rw [← pair_projections F G x]
    have h1 := (hgs (finite F G x)).1 (hf.slice_mem _)
    have h0 : plotSmoothEnvelopingAction F G hG hcalc z.val
        ⟨_, hf.slice_mem (finite F G x)⟩ = 0 :=
      hJ z hz (finite F G x) (hf.slice_mem _)
    rw [h0] at h1
    have h2 := congrFun h1 (infinite F G x)
    rw [Submodule.coe_zero, Pi.zero_apply] at h2
    exact h2.symm
  apply Subtype.ext
  change (plotSmoothEnvelopingAction F G hG hcalc z.val ⟨_, h⟩).val = 0
  rw [(hgs b).2 h, hg0, subgroupConstantTerm_zero]
  rfl

end Unipotent

end Langlands.Global
