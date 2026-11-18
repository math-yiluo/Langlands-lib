import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction
import Langlands.Global.RankinSelberg.DualExpansionRectMeasure
import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.ArchimedeanGL
import Langlands.Topology.RestrictedProductSplit
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.Hecke.AdelicLattice
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Coordinates on adelic rectangular matrices and uniqueness of Haar measure

For a number field `F`, a finite set `S` of finite places and `k m : ℕ`, the additive group
`M_(k,m)(𝔸)` is identified, as a topological group, with
`((∏_v M_(k,m)(ℝ) × ∏_w M_(k,m)(ℂ)) × ∏_(v ∈ S) M_(k,m)(F_v)) × M_(k,m)(𝔸^S)`, where `𝔸^S` is the
restricted product of the completions at the finite places outside `S`. By uniqueness of Haar
measure, the image of `rectangleMeasure F k m` is a constant multiple of any product of Haar
measures on the factors, and integrals of products of local functions, cut off by integrality
outside `S`, factor as that constant times the product of the local integrals.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped ENNReal NNReal RestrictedProduct nonZeroDivisors
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RectangleTate

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

/-! ### Local instances -/

local instance completionMeasurableSpace (v : FinitePlace F) :
    MeasurableSpace (FiniteCompletion F v) := borel _

local instance completionBorelSpace (v : FinitePlace F) :
    BorelSpace (FiniteCompletion F v) := ⟨rfl⟩

local instance completionSecondCountable (v : FinitePlace F) :
    SecondCountableTopology (FiniteCompletion F v) :=
  finiteCompletion_secondCountableTopology F v

local instance completionLocallyCompact (v : FinitePlace F) :
    LocallyCompactSpace (FiniteCompletion F v) :=
  (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem)

local instance integersCompact (v : FinitePlace F) :
    CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)

local instance rectMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rectBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

/-! ### The finite adeles away from `S` -/

variable (S : Finset (FinitePlace F))

/-- The finite adeles away from `S`: the restricted product of the completions `F_v`,
`v ∉ S`, with respect to their rings of integers. -/
abbrev OffAdeles : Type u :=
  Πʳ v : {v : FinitePlace F // v ∉ S},
    [FiniteCompletion F v.1, (v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1))]

local instance offOpen : Fact (∀ v : {v : FinitePlace F // v ∉ S},
    IsOpen (v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

local instance offMeasurableSpace : MeasurableSpace (OffAdeles F S) := borel _

local instance offBorelSpace : BorelSpace (OffAdeles F S) := ⟨rfl⟩

local instance offSecondCountable : SecondCountableTopology (OffAdeles F S) := by
  have := finitePlace_countable F
  exact restrictedProduct_secondCountableTopology _ _ fun _ => Valued.isOpen_valuationSubring _

open Classical in
/-- `𝔸_f ≅ ∏_(v ∈ S) F_v × 𝔸^S`. -/
def split : FiniteAdeles F ≃ₜ (∀ v : S, FiniteCompletion F v.1) × OffAdeles F S :=
  RestrictedProduct.splitFiniteHomeomorph (FiniteCompletion F) (· ∈ S)
    (A := fun v => (v.adicCompletionIntegers F : Set (FiniteCompletion F v)))
    fun _ => Valued.isOpen_valuationSubring _

theorem split_apply_fst (a : FiniteAdeles F) (v : S) : (split F S a).1 v = a v.1 := rfl

theorem split_apply_snd (a : FiniteAdeles F) (v : {v : FinitePlace F // v ∉ S}) :
    (split F S a).2 v = a v.1 := rfl

theorem split_add (a b : FiniteAdeles F) : split F S (a + b) = split F S a + split F S b := rfl

/-! ### The coordinate space -/

variable (k m : ℕ)

/-- `∏_v M_(k,m)(ℝ)` over the real places. -/
abbrev RealPart := {v : InfinitePlace F // v.IsReal} → Fin k → Fin m → ℝ

/-- `∏_w M_(k,m)(ℂ)` over the complex places. -/
abbrev ComplexPart := {v : InfinitePlace F // v.IsComplex} → Fin k → Fin m → ℂ

/-- `∏_(v ∈ S) M_(k,m)(F_v)`. -/
abbrev LocalPart := (v : S) → Fin k → Fin m → FiniteCompletion F v.1

/-- `M_(k,m)(𝔸^S)`. -/
abbrev OffPart := Fin k → Fin m → OffAdeles F S

/-- The coordinate space. -/
abbrev TateSpace :=
  ((RealPart F k m × ComplexPart F k m) × LocalPart F S k m) × OffPart F S k m

/-- The coordinates of an adelic rectangular matrix. -/
def theta : Matrix (Fin k) (Fin m) (Adeles F) ≃ₜ+ TateSpace F S k m where
  toFun x := (((fun v i j => (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1).1 v,
      fun w i j => (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1).2 w),
      fun v i j => (x i j).2 v.1), fun i j => (split F S (x i j).2).2)
  invFun p := Matrix.of fun i j =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (fun v => p.1.1.1 v i j, fun w => p.1.1.2 w i j),
      (split F S).symm (fun v => p.1.2 v i j, p.2 i j)) : Adeles F)
  left_inv x := by
    ext i j
    have h1 : (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1) = (x i j).1 :=
      RingEquiv.symm_apply_apply _ _
    have h2 : (split F S).symm (split F S (x i j).2) = (x i j).2 :=
      Homeomorph.symm_apply_apply _ _
    exact Prod.ext h1 h2
  right_inv p := by
    obtain ⟨⟨⟨pr, pc⟩, ps⟩, py⟩ := p
    have hφ : ∀ i j, InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (fun v => pr v i j, fun w => pc w i j)) = (fun v => pr v i j, fun w => pc w i j) :=
      fun i j => RingEquiv.apply_symm_apply _ _
    have hs : ∀ i j, split F S ((split F S).symm (fun v => ps v i j, py i j)) =
        (fun v => ps v i j, py i j) :=
      fun i j => Homeomorph.apply_symm_apply _ _
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_
    · funext v i j
      exact congrArg (fun z => z.1 v) (hφ i j)
    · funext w i j
      exact congrArg (fun z => z.2 w) (hφ i j)
    · funext v i j
      exact congrArg (fun z => z.1 v) (hs i j)
    · funext i j
      exact congrArg Prod.snd (hs i j)
  map_add' x y := by
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_
    · funext v i j
      exact congrArg (fun z => z.1 v)
        (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i j).1 (y i j).1)
    · funext w i j
      exact congrArg (fun z => z.2 w)
        (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i j).1 (y i j).1)
    · rfl
    · rfl
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_) ?_
    · refine continuous_pi fun v => continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply v).comp (continuous_fst.comp
        ((continuous_infiniteAdeleCoordinates F).comp
          (continuous_fst.comp (continuous_id.matrix_elem i j))))
    · refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply w).comp (continuous_snd.comp
        ((continuous_infiniteAdeleCoordinates F).comp
          (continuous_fst.comp (continuous_id.matrix_elem i j))))
    · refine continuous_pi fun v => continuous_pi fun i => continuous_pi fun j => ?_
      exact (RestrictedProduct.continuous_eval v.1).comp
        (continuous_snd.comp (continuous_id.matrix_elem i j))
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_snd.comp ((split F S).continuous.comp
        (continuous_snd.comp (continuous_id.matrix_elem i j)))
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_infiniteAdeleCoordinates_symm F).comp (by fun_prop)
    · exact (split F S).symm.continuous.comp (by fun_prop)

theorem theta_apply_snd (x : Matrix (Fin k) (Fin m) (Adeles F)) (i : Fin k) (j : Fin m)
    (v : {v : FinitePlace F // v ∉ S}) :
    (theta F S k m x).2 i j v = finiteProjection F v.1 (x i j) := rfl

/-! ### The compact open subgroup `M_(k,m)(∏_(v ∉ S) 𝒪_v)` -/

/-- The elements of `𝔸^S` integral at every place. -/
def offIntegers : Set (OffAdeles F S) := {a | ∀ v, a v ∈ v.1.adicCompletionIntegers F}

theorem isCompact_offIntegers : IsCompact (offIntegers F S) := by
  have : ∀ v : {v : FinitePlace F // v ∉ S},
      CompactSpace ((v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1))) :=
    fun v => isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v.1)
  have h := isCompact_range
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : {v : FinitePlace F // v ∉ S} => FiniteCompletion F v.1)
      (A := fun v => (v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1)))
      (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_offIntegers : IsOpen (offIntegers F S) :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

/-- `M_(k,m)(∏_(v ∉ S) 𝒪_v)` inside `M_(k,m)(𝔸^S)`. -/
def offSet : Set (OffPart F S k m) := univ.pi fun _ => univ.pi fun _ => offIntegers F S

theorem mem_offSet (y : OffPart F S k m) :
    y ∈ offSet F S k m ↔ ∀ i j v, y i j v ∈ v.1.adicCompletionIntegers F := by
  simp only [offSet, mem_univ_pi]
  rfl

theorem isCompact_offSet : IsCompact (offSet F S k m) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_offIntegers F S

theorem isOpen_offSet : IsOpen (offSet F S k m) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_set_pi finite_univ fun _ _ => isOpen_offIntegers F S

theorem measurableSet_offSet : MeasurableSet (offSet F S k m) :=
  (isOpen_offSet F S k m).measurableSet

/-- `M_(k,m)(∏_(v ∉ S) 𝒪_v)` as a compact set with nonempty interior. -/
def offCompacts : TopologicalSpace.PositiveCompacts (OffPart F S k m) where
  carrier := offSet F S k m
  isCompact' := isCompact_offSet F S k m
  interior_nonempty' := by
    rw [(isOpen_offSet F S k m).interior_eq]
    exact ⟨0, (mem_offSet F S k m 0).mpr fun _ _ v => (v.1.adicCompletionIntegers F).zero_mem⟩

/-- The Haar measure of `M_(k,m)(𝔸^S)` giving `M_(k,m)(∏_(v ∉ S) 𝒪_v)` mass one. -/
def offMeasure : Measure (OffPart F S k m) := Measure.addHaarMeasure (offCompacts F S k m)

instance offMeasure_isAddHaarMeasure : (offMeasure F S k m).IsAddHaarMeasure := by
  unfold offMeasure
  infer_instance

theorem offMeasure_offSet : offMeasure F S k m (offSet F S k m) = 1 :=
  Measure.addHaarMeasure_self

/-! ### Uniqueness of Haar measure -/

local instance realPartSC : SecondCountableTopology (RealPart F k m) := inferInstance
local instance realPartBorel : BorelSpace (RealPart F k m) := inferInstance
local instance complexPartSC : SecondCountableTopology (ComplexPart F k m) := inferInstance
local instance complexPartBorel : BorelSpace (ComplexPart F k m) := inferInstance
local instance localPartSC : SecondCountableTopology (LocalPart F S k m) := inferInstance
local instance localPartBorel : BorelSpace (LocalPart F S k m) := inferInstance
local instance offPartSC : SecondCountableTopology (OffPart F S k m) := inferInstance
local instance offPartBorel : BorelSpace (OffPart F S k m) := inferInstance
local instance archSC : SecondCountableTopology (RealPart F k m × ComplexPart F k m) :=
  inferInstance
local instance archBorel : BorelSpace (RealPart F k m × ComplexPart F k m) := Prod.borelSpace
local instance semiSC :
    SecondCountableTopology ((RealPart F k m × ComplexPart F k m) × LocalPart F S k m) :=
  inferInstance
local instance semiBorel :
    BorelSpace ((RealPart F k m × ComplexPart F k m) × LocalPart F S k m) := Prod.borelSpace
local instance tateSC : SecondCountableTopology (TateSpace F S k m) := inferInstance
local instance tateBorel : BorelSpace (TateSpace F S k m) := Prod.borelSpace
local instance tateLC : LocallyCompactSpace (TateSpace F S k m) := inferInstance
local instance completionMeasurableAdd (v : FinitePlace F) :
    MeasurableAdd (FiniteCompletion F v) := inferInstance
local instance realPartMeasurableAdd : MeasurableAdd (RealPart F k m) := inferInstance
local instance complexPartMeasurableAdd : MeasurableAdd (ComplexPart F k m) := inferInstance
local instance localPartMeasurableAdd : MeasurableAdd (LocalPart F S k m) := inferInstance
local instance offPartMeasurableAdd : MeasurableAdd (OffPart F S k m) := inferInstance
local instance archMeasurableAdd : MeasurableAdd (RealPart F k m × ComplexPart F k m) :=
  inferInstance
local instance semiContinuousAdd :
    ContinuousAdd ((RealPart F k m × ComplexPart F k m) × LocalPart F S k m) := inferInstance
local instance semiMeasurableAdd :
    MeasurableAdd ((RealPart F k m × ComplexPart F k m) × LocalPart F S k m) :=
  ContinuousAdd.measurableAdd

/-- Matrices of a Haar measure form a Haar measure. -/
theorem isAddHaarMeasure_pipi {β : Type*} [AddGroup β] [TopologicalSpace β] [MeasurableSpace β]
    [MeasurableAdd β] (μ : Measure β) [μ.IsAddHaarMeasure] [SigmaFinite μ] :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μ).IsAddHaarMeasure := by
  have : (Measure.pi fun _ : Fin m => μ).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

/-- Families of matrices of Haar measures form a Haar measure. -/
theorem isAddHaarMeasure_pipipi {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, AddGroup (β i)]
    [∀ i, TopologicalSpace (β i)] [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableAdd (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, (μ i).IsAddHaarMeasure] [∀ i, SigmaFinite (μ i)] :
    (Measure.pi fun i => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m =>
      μ i).IsAddHaarMeasure := by
  have := fun i => isAddHaarMeasure_pipi k m (μ i)
  exact Measure.pi.isAddHaarMeasure _

open scoped Classical

variable {F S k m}

/-- The product of Haar measures `μR v`, `μC w`, `ν v` on the factors and of `offMeasure`. -/
def productMeasure (μR : {v : InfinitePlace F // v.IsReal} → Measure ℝ)
    (μC : {v : InfinitePlace F // v.IsComplex} → Measure ℂ)
    (ν : ∀ v : S, Measure (FiniteCompletion F v.1)) : Measure (TateSpace F S k m) :=
  (((Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v).prod
      (Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w)).prod
    (Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v)).prod
    (offMeasure F S k m)

variable (μR : {v : InfinitePlace F // v.IsReal} → Measure ℝ)
  (μC : {v : InfinitePlace F // v.IsComplex} → Measure ℂ)
  (ν : ∀ v : S, Measure (FiniteCompletion F v.1))
  [∀ v, (μR v).IsAddHaarMeasure] [∀ w, (μC w).IsAddHaarMeasure] [∀ v, (ν v).IsAddHaarMeasure]

instance productMeasure_isAddHaarMeasure :
    (productMeasure (k := k) (m := m) μR μC ν).IsAddHaarMeasure := by
  have h1 := isAddHaarMeasure_pipipi k m μR
  have h2 := isAddHaarMeasure_pipipi k m μC
  have h3 := isAddHaarMeasure_pipipi k m ν
  have : SigmaFinite (Measure.pi fun v => Measure.pi fun _ : Fin k =>
      Measure.pi fun _ : Fin m => μR v) := inferInstance
  have : SigmaFinite (Measure.pi fun w => Measure.pi fun _ : Fin k =>
      Measure.pi fun _ : Fin m => μC w) := inferInstance
  have : SigmaFinite (Measure.pi fun v => Measure.pi fun _ : Fin k =>
      Measure.pi fun _ : Fin m => ν v) := inferInstance
  have h12 := Measure.prod.instIsAddHaarMeasure
    (Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v)
    (Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w)
  have h123 := Measure.prod.instIsAddHaarMeasure
    ((Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v).prod
      (Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w))
    (Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v)
  exact Measure.prod.instIsAddHaarMeasure _ (offMeasure F S k m)

variable [CompactSpace (AdeleQuotient F)]

variable (F S k m) in
instance map_theta_isAddHaarMeasure :
    (Measure.map (theta F S k m) (rectangleMeasure F k m)).IsAddHaarMeasure :=
  (theta F S k m).toAddEquiv.isAddHaarMeasure_map (rectangleMeasure F k m)
    (theta F S k m).continuous (theta F S k m).symm.continuous

/-- The scalar relating the image of `rectangleMeasure` to the product measure. -/
def scalar : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.map (theta F S k m) (rectangleMeasure F k m))
    (productMeasure μR μC ν)

theorem map_theta_eq :
    Measure.map (theta F S k m) (rectangleMeasure F k m) =
      (scalar (F := F) (S := S) (k := k) (m := m) μR μC ν : ℝ≥0∞) • productMeasure μR μC ν := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul
    (Measure.map (theta F S k m) (rectangleMeasure F k m)) (productMeasure μR μC ν)]
  exact ENNReal.smul_def _ _

variable (F S k m) in
omit [CompactSpace (AdeleQuotient F)] in
theorem measurableEmbedding_theta : MeasurableEmbedding (theta F S k m) :=
  (theta F S k m).toHomeomorph.measurableEmbedding

theorem integral_theta (G : TateSpace F S k m → ℂ) :
    ∫ x, G (theta F S k m x) ∂rectangleMeasure F k m =
      ((scalar (F := F) (S := S) (k := k) (m := m) μR μC ν : ℝ) : ℂ) *
        ∫ z, G z ∂productMeasure μR μC ν := by
  rw [← (measurableEmbedding_theta F S k m).integral_map, map_theta_eq μR μC ν,
    integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]

/-! ### Integrals of products of local functions -/

variable (hR : {v : InfinitePlace F // v.IsReal} → Matrix (Fin k) (Fin m) ℝ → ℂ)
  (hC : {v : InfinitePlace F // v.IsComplex} → Matrix (Fin k) (Fin m) ℂ → ℂ)
  (hS : ∀ v : S, Matrix (Fin k) (Fin m) (FiniteCompletion F v.1) → ℂ)

/-- The product of the local functions, cut off by integrality outside `S`, on the coordinate
space. -/
def tensor (z : TateSpace F S k m) : ℂ :=
  (∏ v, hR v (z.1.1.1 v)) * (∏ w, hC w (z.1.1.2 w)) * (∏ v, hS v (z.1.2 v)) *
    (offSet F S k m).indicator (fun _ => (1 : ℂ)) z.2

omit [CompactSpace (AdeleQuotient F)] in
theorem mem_rectIntegralOutside_iff (x : Matrix (Fin k) (Fin m) (Adeles F)) :
    x ∈ rectIntegralOutside F k m S ↔ (theta F S k m x).2 ∈ offSet F S k m := by
  rw [mem_offSet]
  constructor
  · intro h i j v
    exact h v.1 v.2 i j
  · intro h v hv i j
    exact h i j ⟨v, hv⟩

omit [CompactSpace (AdeleQuotient F)] in
theorem indicator_eq_tensor (x : Matrix (Fin k) (Fin m) (Adeles F)) :
    (rectIntegralOutside F k m S).indicator (fun x =>
        (∏ v, hR v (realRectCoordinates F v x)) * (∏ w, hC w (complexRectCoordinates F w x)) *
          ∏ v : S, hS v (localRectCoordinates F v.1 x)) x =
      tensor hR hC hS (theta F S k m x) := by
  unfold tensor
  by_cases h : (theta F S k m x).2 ∈ offSet F S k m
  · rw [Set.indicator_of_mem ((mem_rectIntegralOutside_iff x).mpr h), Set.indicator_of_mem h,
      mul_one]
    rfl
  · rw [Set.indicator_of_notMem (fun h' => h ((mem_rectIntegralOutside_iff x).mp h')),
      Set.indicator_of_notMem h, mul_zero]

omit [CompactSpace (AdeleQuotient F)] in
theorem integral_tensor :
    ∫ z, tensor hR hC hS z ∂productMeasure μR μC ν =
      (∏ v, ∫ y : Fin k → Fin m → ℝ, hR v y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v)) *
        (∏ w, ∫ y : Fin k → Fin m → ℂ, hC w y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w)) *
        ∏ v, ∫ y : Fin k → Fin m → FiniteCompletion F v.1, hS v y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v) := by
  set PR := Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v
  set PC := Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w
  set PS := Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v
  have sR : ∀ v, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v) :=
    fun _ => inferInstance
  have sC : ∀ w, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w) :=
    fun _ => inferInstance
  have sS : ∀ v, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v) :=
    fun _ => inferInstance
  have sPR : SigmaFinite PR := inferInstance
  have sPC : SigmaFinite PC := inferInstance
  have sPS : SigmaFinite PS := inferInstance
  have sPRC : SigmaFinite (PR.prod PC) := inferInstance
  have sPRCS : SigmaFinite ((PR.prod PC).prod PS) := inferInstance
  have h1 := integral_prod_mul (μ := (PR.prod PC).prod PS) (ν := offMeasure F S k m)
    (fun w : (RealPart F k m × ComplexPart F k m) × LocalPart F S k m =>
      (∏ v, hR v (w.1.1 v)) * (∏ w', hC w' (w.1.2 w')) * ∏ v, hS v (w.2 v))
    ((offSet F S k m).indicator fun _ => (1 : ℂ))
  have h2 := integral_prod_mul (μ := PR.prod PC) (ν := PS)
    (fun w : RealPart F k m × ComplexPart F k m => (∏ v, hR v (w.1 v)) * ∏ w', hC w' (w.2 w'))
    (fun s : LocalPart F S k m => ∏ v, hS v (s v))
  have h3 := integral_prod_mul (μ := PR) (ν := PC) (fun r : RealPart F k m => ∏ v, hR v (r v))
    (fun c : ComplexPart F k m => ∏ w, hC w (c w))
  have h4 := integral_fintype_prod_eq_prod (fun v (y : Fin k → Fin m → ℝ) => hR v y)
    (μ := fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v)
  have h5 := integral_fintype_prod_eq_prod (fun w (y : Fin k → Fin m → ℂ) => hC w y)
    (μ := fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w)
  have h6 := integral_fintype_prod_eq_prod
    (fun (v : S) (y : Fin k → Fin m → FiniteCompletion F v.1) => hS v y)
    (μ := fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v)
  have h7 : ∫ y, (offSet F S k m).indicator (fun _ => (1 : ℂ)) y ∂offMeasure F S k m = 1 := by
    rw [integral_indicator_const _ (measurableSet_offSet F S k m), Measure.real,
      offMeasure_offSet, ENNReal.toReal_one, one_smul]
  have h : productMeasure μR μC ν = ((PR.prod PC).prod PS).prod (offMeasure F S k m) := rfl
  rw [h]
  unfold tensor
  rw [h1, h7, mul_one, h2, h3, h4, h5, h6]

theorem integral_indicator_rect :
    ∫ x, (rectIntegralOutside F k m S).indicator (fun x =>
        (∏ v, hR v (realRectCoordinates F v x)) * (∏ w, hC w (complexRectCoordinates F w x)) *
          ∏ v : S, hS v (localRectCoordinates F v.1 x)) x ∂rectangleMeasure F k m =
      ((scalar (F := F) (S := S) (k := k) (m := m) μR μC ν : ℝ) : ℂ) *
        ((∏ v, ∫ y : Fin k → Fin m → ℝ, hR v y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v)) *
        (∏ w, ∫ y : Fin k → Fin m → ℂ, hC w y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w)) *
        ∏ v, ∫ y : Fin k → Fin m → FiniteCompletion F v.1, hS v y
          ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v)) := by
  rw [← integral_tensor μR μC ν hR hC hS, ← integral_theta μR μC ν]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => indicator_eq_tensor hR hC hS x)

/-! ### A fundamental domain for `M_(k,m)(F)` in `M_(k,m)(𝔸)` -/

variable (F) in
/-- The ring of integers, as the fractional ideal `latticeIdeal 0` of the Hecke development. -/
abbrev integerIdeal : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Hecke.latticeIdeal (0 : FinitePlace F →₀ ℤ)

variable (F) in
/-- The fundamental parallelepiped `D_∞` of the lattice of integers in the mixed space. -/
abbrev archDomain : Set (mixedEmbedding.mixedSpace F) :=
  ZSpan.fundamentalDomain (mixedEmbedding.fractionalIdealLatticeBasis F (integerIdeal F))

omit [CompactSpace (AdeleQuotient F)] in
theorem mem_integerIdeal_iff (γ : F) :
    γ ∈ (integerIdeal F : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v : FinitePlace F, algebraMap F (FiniteCompletion F v) γ ∈ v.adicCompletionIntegers F := by
  rw [Hecke.mem_latticeIdeal_iff]
  refine forall_congr' fun v => ?_
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  change _ ↔ Valued.v ((γ : v.adicCompletion F)) ≤ 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simp

variable (F) in
/-- `D_∞ × ∏_v 𝒪_v ⊆ 𝔸`. -/
def adeleDomain : Set (Adeles F) :=
  {a | InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 ∈ archDomain F ∧
    ∀ v, a.2 v ∈ v.adicCompletionIntegers F}

omit [CompactSpace (AdeleQuotient F)] in
theorem ringEquiv_mixedSpace_add_diagonal (γ : F) (a : Adeles F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (diagonal F γ + a).1 =
      mixedEmbedding F γ + InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F ((diagonal F γ).1 + a.1) = _
  rw [map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem finite_add_diagonal (γ : F) (a : Adeles F) (v : FinitePlace F) :
    (diagonal F γ + a).2 v = algebraMap F (FiniteCompletion F v) γ + a.2 v := rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem eq_of_add_mem_adeleDomain {a : Adeles F} {γ₁ γ₂ : F}
    (h₁ : diagonal F γ₁ + a ∈ adeleDomain F) (h₂ : diagonal F γ₂ + a ∈ adeleDomain F) :
    γ₁ = γ₂ := by
  set b := diagonal F γ₂ + a with hb
  have hab : diagonal F γ₁ + a = diagonal F (γ₁ - γ₂) + b := by
    rw [hb, map_sub]
    abel
  rw [hab] at h₁
  have hI : γ₁ - γ₂ ∈ (integerIdeal F : FractionalIdeal (𝓞 F)⁰ F) := by
    refine (mem_integerIdeal_iff _).mpr fun v => ?_
    have h := sub_mem (h₁.2 v) (h₂.2 v)
    rwa [finite_add_diagonal, add_sub_cancel_right] at h
  have hspan : mixedEmbedding F (γ₁ - γ₂) ∈ Submodule.span ℤ
      (Set.range (mixedEmbedding.fractionalIdealLatticeBasis F (integerIdeal F))) :=
    (mixedEmbedding.mem_span_fractionalIdealLatticeBasis F _).mpr ⟨_, hI, rfl⟩
  obtain ⟨w, -, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    (mixedEmbedding.fractionalIdealLatticeBasis F (integerIdeal F))
    (InfiniteAdeleRing.ringEquiv_mixedSpace F b.1)
  have e1 := huniq ⟨_, hspan⟩ (by
    change mixedEmbedding F (γ₁ - γ₂) + _ ∈ _
    rw [← ringEquiv_mixedSpace_add_diagonal]
    exact h₁.1)
  have e0 := huniq 0 (by
    simp only [zero_vadd]
    exact h₂.1)
  have h0 : mixedEmbedding F (γ₁ - γ₂) = 0 := congrArg Subtype.val (e1.trans e0.symm)
  rw [map_eq_zero_iff _ (NumberField.mixedEmbedding_injective F), sub_eq_zero] at h0
  exact h0

omit [CompactSpace (AdeleQuotient F)] in
theorem exists_add_mem_adeleDomain (a : Adeles F) : ∃ γ : F, diagonal F γ + a ∈ adeleDomain F := by
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles a.2
  set b := diagonal F (-x) + a with hb
  have hbf : ∀ v, b.2 v ∈ v.adicCompletionIntegers F := by
    intro v
    have h := (mem_integralFiniteAdeles F _).mp hx v
    rw [hb, finite_add_diagonal, map_neg, neg_add_eq_sub]
    exact h
  obtain ⟨⟨w, hw⟩, hwD, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    (mixedEmbedding.fractionalIdealLatticeBasis F (integerIdeal F))
    (InfiniteAdeleRing.ringEquiv_mixedSpace F b.1)
  obtain ⟨δ, hδ, rfl⟩ := (mixedEmbedding.mem_span_fractionalIdealLatticeBasis F _).mp hw
  refine ⟨δ + -x, ?_, fun v => ?_⟩
  · rw [map_add, add_assoc, ← hb, ringEquiv_mixedSpace_add_diagonal]
    exact hwD
  · rw [map_add, add_assoc, ← hb, finite_add_diagonal]
    exact add_mem ((mem_integerIdeal_iff δ).mp hδ v) (hbf v)

variable (F k m) in
/-- `M_(k,m)(D_∞ × ∏_v 𝒪_v)`. -/
def rectAdeleDomain : Set (Matrix (Fin k) (Fin m) (Adeles F)) :=
  {x | ∀ i j, x i j ∈ adeleDomain F}

omit [CompactSpace (AdeleQuotient F)] in
theorem existsUnique_add_mem_rectAdeleDomain (x : Matrix (Fin k) (Fin m) (Adeles F)) :
    ∃! c : Unfolding.rectLattice F k m,
      (c : Matrix (Fin k) (Fin m) (Adeles F)) + x ∈ rectAdeleDomain F k m := by
  choose γ hγ using fun i j => exists_add_mem_adeleDomain (x i j)
  refine ⟨⟨(Matrix.of γ).map (diagonal F), ⟨Matrix.of γ, rfl⟩⟩, fun i j => hγ i j, ?_⟩
  rintro ⟨c, C, rfl⟩ hc
  apply Subtype.ext
  change C.map (diagonal F) = (Matrix.of γ).map (diagonal F)
  ext i j
  exact congrArg (diagonal F)
    (eq_of_add_mem_adeleDomain (a := x i j) (γ₁ := C i j) (hc i j) (hγ i j))

variable (F k m) in
/-- The archimedean part `{p | ∀ i j, p_(i,j) ∈ D_∞}` of the coordinates of
`rectAdeleDomain`. -/
def archSet : Set (RealPart F k m × ComplexPart F k m) :=
  {p | ∀ i j, ((fun v => p.1 v i j, fun w => p.2 w i j) : mixedEmbedding.mixedSpace F) ∈
    archDomain F}

variable (F S k m) in
/-- `∏_(v ∈ S) M_(k,m)(𝒪_v)`. -/
def localSet : Set (LocalPart F S k m) :=
  {s | ∀ v i j, s v i j ∈ v.1.adicCompletionIntegers F}

omit [CompactSpace (AdeleQuotient F)] in
theorem mem_theta_preimage (x : Matrix (Fin k) (Fin m) (Adeles F)) :
    theta F S k m x ∈ (archSet F k m ×ˢ localSet F S k m) ×ˢ offSet F S k m ↔
      x ∈ rectAdeleDomain F k m := by
  rw [Set.mem_prod, Set.mem_prod, mem_offSet]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ i j
    exact ⟨h1 i j, fun v => if hv : v ∈ S then h2 ⟨v, hv⟩ i j else h3 i j ⟨v, hv⟩⟩
  · intro h
    exact ⟨⟨fun i j => (h i j).1, fun v i j => (h i j).2 v.1⟩, fun i j v => (h i j).2 v.1⟩

omit [CompactSpace (AdeleQuotient F)] in
theorem localSet_eq : localSet F S k m =
    univ.pi fun v : S => univ.pi fun _ : Fin k => univ.pi fun _ : Fin m =>
      (v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1)) := by
  ext s
  simp [localSet]

omit [CompactSpace (AdeleQuotient F)] in
theorem archSet_eq : archSet F k m =
    (fun (p : RealPart F k m × ComplexPart F k m) (i : Fin k) (j : Fin m) =>
      ((fun v => p.1 v i j), (fun w => p.2 w i j))) ⁻¹'
      (univ.pi fun _ : Fin k => univ.pi fun _ : Fin m => archDomain F) := by
  ext p
  simp [archSet]

omit [CompactSpace (AdeleQuotient F)] in
theorem measurableSet_archSet : MeasurableSet (archSet F k m) := by
  rw [archSet_eq]
  have hD : MeasurableSet (archDomain F) := ZSpan.fundamentalDomain_measurableSet _
  exact (measurePreserving_rearrange k m (fun _ => (volume : Measure ℝ))
    (fun _ => (volume : Measure ℂ))).measurable
    (MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hD)

omit [CompactSpace (AdeleQuotient F)] in
theorem measurableSet_localSet : MeasurableSet (localSet F S k m) := by
  rw [localSet_eq]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ =>
    MeasurableSet.univ_pi fun _ => (Valued.isOpen_valuationSubring _).measurableSet

omit [CompactSpace (AdeleQuotient F)] in
theorem measurableSet_tateSet :
    MeasurableSet ((archSet F k m ×ˢ localSet F S k m) ×ˢ offSet F S k m) :=
  (measurableSet_archSet.prod measurableSet_localSet).prod (measurableSet_offSet F S k m)

omit [CompactSpace (AdeleQuotient F)] in
theorem theta_preimage_eq :
    theta F S k m ⁻¹' ((archSet F k m ×ˢ localSet F S k m) ×ˢ offSet F S k m) =
      rectAdeleDomain F k m :=
  Set.ext fun x => mem_theta_preimage x

omit [CompactSpace (AdeleQuotient F)] in
theorem measurableSet_rectAdeleDomain : MeasurableSet (rectAdeleDomain F k m) := by
  have h := (measurableEmbedding_theta F (∅ : Finset (FinitePlace F)) k m).measurable
    (measurableSet_tateSet (S := ∅))
  rwa [theta_preimage_eq] at h

omit [CompactSpace (AdeleQuotient F)] in
theorem isAddFundamentalDomain_rectAdeleDomain
    (μ : Measure (Matrix (Fin k) (Fin m) (Adeles F))) :
    IsAddFundamentalDomain (Unfolding.rectLattice F k m) (rectAdeleDomain F k m) μ := by
  apply IsAddFundamentalDomain.mk' measurableSet_rectAdeleDomain.nullMeasurableSet
  intro x
  obtain ⟨c, hc, hu⟩ := existsUnique_add_mem_rectAdeleDomain x
  exact ⟨c, hc, fun c' hc' => hu c' hc'⟩

theorem rectangleMeasure_rectAdeleDomain :
    rectangleMeasure F k m (rectAdeleDomain F k m) = 1 := by
  rw [(isAddFundamentalDomain_rectAdeleDomain _).measure_eq
    (Unfolding.isAddFundamentalDomain_rectDomain F k m _)]
  exact Unfolding.rectangleMeasure_rectDomain F k m

omit [NumberField F] in
theorem prod_const_rect (c : ℝ≥0∞) : (∏ _i : Fin k, ∏ _j : Fin m, c) = c ^ (k * m) := by
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul, mul_comm]

omit [CompactSpace (AdeleQuotient F)] in
theorem productMeasure_tateSet :
    productMeasure μR μC ν ((archSet F k m ×ˢ localSet F S k m) ×ˢ offSet F S k m) =
      ((Measure.pi μR).prod (Measure.pi μC) (archDomain F)) ^ (k * m) *
        (∏ v, ν v (v.1.adicCompletionIntegers F)) ^ (k * m) := by
  set PR := Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v
  set PC := Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w
  set PS := Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v
  have sR : ∀ v, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μR v) :=
    fun _ => inferInstance
  have sC : ∀ w, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μC w) :=
    fun _ => inferInstance
  have sS : ∀ v, SigmaFinite (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν v) :=
    fun _ => inferInstance
  have sS' : ∀ v (_ : Fin k), SigmaFinite (Measure.pi fun _ : Fin m => ν v) :=
    fun _ _ => inferInstance
  have sPC : SigmaFinite PC := inferInstance
  have sPS : SigmaFinite PS := inferInstance
  have sV : SigmaFinite ((Measure.pi μR).prod (Measure.pi μC)) := inferInstance
  have h : productMeasure μR μC ν = ((PR.prod PC).prod PS).prod (offMeasure F S k m) := rfl
  have hD : MeasurableSet (archDomain F) := ZSpan.fundamentalDomain_measurableSet _
  rw [h, Measure.prod_prod, Measure.prod_prod, offMeasure_offSet, mul_one, archSet_eq,
    (measurePreserving_rearrange k m μR μC).measure_preimage
      (MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hD).nullMeasurableSet,
    localSet_eq, Measure.pi_pi, Measure.pi_pi]
  rw [prod_const_rect, ← Finset.prod_pow]
  congr 1
  simp only [PS, Measure.pi_pi, prod_const_rect]

theorem scalar_eq_one
    (hnorm : (Measure.pi μR).prod (Measure.pi μC) (archDomain F) *
      ∏ v, ν v (v.1.adicCompletionIntegers F) = 1) :
    scalar (F := F) (S := S) (k := k) (m := m) μR μC ν = 1 := by
  have h1 := rectangleMeasure_rectAdeleDomain (F := F) (k := k) (m := m)
  rw [← theta_preimage_eq (S := S),
    ← Measure.map_apply (measurableEmbedding_theta F S k m).measurable measurableSet_tateSet,
    map_theta_eq μR μC ν, Measure.smul_apply, productMeasure_tateSet, ← mul_pow, hnorm, one_pow,
    smul_eq_mul, mul_one] at h1
  exact_mod_cast h1

end Langlands.Global.RankinSelbergGlobal.RectangleTate
