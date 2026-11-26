import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Representation.Shahidi.UnramifiedOpenCellSumStatement

/-! # One-place decomposition and exhaustion for the partial open-cell integrals

Measure-theoretic lemmas for the unramified factorization of the open-cell integral: adelic
matrices supported at one finite place, the decomposition of the matrices integral outside
`insert v A` into translates of the matrices integral outside `A`, the resulting one-place
step for set integrals, and the exhaustion of `M(𝔸)` by these sets. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellExhaustion

open MeasureTheory NumberField Filter

variable {F : Type u} [Field F] [NumberField F]

section LocalAdele

open scoped Classical

/-- The adele with component `x` at the finite place `v` and `0` at every other place. -/
def localAdele (v : FinitePlace F) (x : FiniteCompletion F v) : Adeles F :=
  (0, RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v x)

@[simp] theorem finiteProjection_localAdele (v : FinitePlace F) (x : FiniteCompletion F v) :
    finiteProjection F v (localAdele v x) = x := by
  change (Pi.single v x : ∀ w : FinitePlace F, FiniteCompletion F w) v = x
  simp

theorem finiteProjection_localAdele_of_ne {v w : FinitePlace F} (h : w ≠ v)
    (x : FiniteCompletion F v) : finiteProjection F w (localAdele v x) = 0 := by
  change (Pi.single v x : ∀ w : FinitePlace F, FiniteCompletion F w) w = 0
  simp [h]

theorem localAdele_add (v : FinitePlace F) (x y : FiniteCompletion F v) :
    localAdele v (x + y) = localAdele v x + localAdele v y := by
  refine Prod.ext (by change (0 : InfiniteAdeleRing F) = 0 + 0; rw [add_zero]) ?_
  exact RestrictedProduct.single_add _ v x y

/-- The adelic matrix with component `y` at the finite place `v` and `0` elsewhere. -/
def localMatrix {a b : ℕ} (v : FinitePlace F) (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    Matrix (Fin a) (Fin b) (Adeles F) :=
  fun i j => localAdele v (y i j)

theorem localMatrix_add {a b : ℕ} (v : FinitePlace F)
    (y z : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    localMatrix v (y + z) = localMatrix v y + localMatrix v z := by
  funext i j
  exact localAdele_add v (y i j) (z i j)

end LocalAdele

/-- The component at the finite place `v` of an adelic matrix. -/
def matrixComponent {a b : ℕ} (v : FinitePlace F) (Y : Matrix (Fin a) (Fin b) (Adeles F)) :
    Matrix (Fin a) (Fin b) (FiniteCompletion F v) :=
  fun i j => finiteProjection F v (Y i j)

@[simp] theorem matrixComponent_localMatrix {a b : ℕ} (v : FinitePlace F)
    (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    matrixComponent v (localMatrix v y) = y := by
  funext i j
  exact finiteProjection_localAdele v (y i j)

theorem matrixComponent_localMatrix_of_ne {a b : ℕ} {v w : FinitePlace F} (h : w ≠ v)
    (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    matrixComponent w (localMatrix v y) = 0 := by
  funext i j
  exact finiteProjection_localAdele_of_ne h (y i j)

theorem matrixComponent_add {a b : ℕ} (v : FinitePlace F)
    (Y Z : Matrix (Fin a) (Fin b) (Adeles F)) :
    matrixComponent v (Y + Z) = matrixComponent v Y + matrixComponent v Z := by
  funext i j
  exact map_add (finiteProjection F v) (Y i j) (Z i j)

theorem matrixComponent_sub {a b : ℕ} (v : FinitePlace F)
    (Y Z : Matrix (Fin a) (Fin b) (Adeles F)) :
    matrixComponent v (Y - Z) = matrixComponent v Y - matrixComponent v Z := by
  funext i j
  exact map_sub (finiteProjection F v) (Y i j) (Z i j)

section Integral

variable (r t : ℕ)

theorem mem_integralOutside_iff (S : Finset (FinitePlace F))
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    Y ∈ integralOutside F r t S ↔
      ∀ v ∉ S, ∀ i j, matrixComponent v Y i j ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem integralOutside_mono {S S' : Finset (FinitePlace F)} (h : S ⊆ S') :
    integralOutside F r t S ⊆ integralOutside F r t S' :=
  fun _ hY v hv => hY v (fun hvS => hv (h hvS))

/-- The integers of the completion are the integers of the canonical valuation of
`padicField v`. -/
theorem mem_adicCompletionIntegers_iff_canonical (v : FinitePlace F)
    (x : FiniteCompletion F v) :
    x ∈ v.adicCompletionIntegers F ↔
      x ∈ (CompletionPadic.padicField v).canonicalTopologicalData.Integers := by
  have h := RankinSelbergGlobal.LocalPointFactorization.integer_eq_of_isEquiv
    (RankinSelbergGlobal.LocalPointFactorization.valued_isEquiv_canonical v)
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valuation.mem_integer_iff, h]

/-- The quotient of `M_((t+1)×(r+1))(F_v)` by the integral matrices, as in
`Shahidi.UnramifiedOpenCellSumStatement`. -/
abbrev LocalQuotient (v : FinitePlace F) :=
  Matrix (Fin (t + 1)) (Fin (r + 1)) (CompletionPadic.padicField v).Carrier ⧸
    Shahidi.integralMatrices (CompletionPadic.padicField v) (t + 1) (r + 1)

theorem mem_integralMatrices_iff (v : FinitePlace F)
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v)) :
    y ∈ Shahidi.integralMatrices (CompletionPadic.padicField v) (t + 1) (r + 1) ↔
      ∀ i j, y i j ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h i j
    exact (mem_adicCompletionIntegers_iff_canonical v _).2
      (h i (Set.mem_univ _) j (Set.mem_univ _))
  · intro h i _ j _
    exact (mem_adicCompletionIntegers_iff_canonical v _).1 (h i j)

theorem isOpen_integralMatrices (v : FinitePlace F) :
    IsOpen (Shahidi.integralMatrices (CompletionPadic.padicField v) (t + 1) (r + 1) :
      Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v))) := by
  have h : (Shahidi.integralMatrices (CompletionPadic.padicField v) (t + 1) (r + 1) :
      Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v))) =
      ⋂ i, ⋂ j, (fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v) => y i j) ⁻¹'
        (v.adicCompletionIntegers F : Set (FiniteCompletion F v)) := by
    ext y
    rw [SetLike.mem_coe, mem_integralMatrices_iff]
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (Valued.isOpen_integer _).preimage ((continuous_apply j).comp (continuous_apply i))

instance countable_localQuotient (v : FinitePlace F) : Countable (LocalQuotient r t v) := by
  have := finiteCompletion_separableSpace F v
  have : TopologicalSpace.SeparableSpace
      (Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v)) :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (Fin (t + 1) → Fin (r + 1) →
      FiniteCompletion F v))
  have : DiscreteTopology (LocalQuotient r t v) :=
    QuotientAddGroup.discreteTopology (isOpen_integralMatrices r t v)
  have : TopologicalSpace.SeparableSpace (LocalQuotient r t v) :=
    (QuotientAddGroup.isQuotientMap_mk _).separableSpace
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem continuous_matrixComponent {a b : ℕ} (v : FinitePlace F) :
    Continuous (matrixComponent (a := a) (b := b) v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp ((continuous_apply j).comp (continuous_apply i)))

theorem isClosed_integralOutside (S : Finset (FinitePlace F)) :
    IsClosed (integralOutside F r t S) := by
  have h : integralOutside F r t S = ⋂ v : {v : FinitePlace F // v ∉ S}, ⋂ i, ⋂ j,
      (fun Y => matrixComponent v.1 Y i j) ⁻¹'
        (v.1.adicCompletionIntegers F : Set (FiniteCompletion F v.1)) := by
    ext Y
    simp only [mem_integralOutside_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
      Subtype.forall]
  rw [h]
  refine isClosed_iInter fun v => isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact (Valued.isClosed_integer _).preimage
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_matrixComponent v.1)))

/-- The translate of `integralOutside F r t A` by the local matrix of the representative of
`y` at `v`. -/
def cell (A : Finset (FinitePlace F)) (v : FinitePlace F) (y : LocalQuotient r t v) :
    Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  (fun Z => localMatrix v (Quotient.out y) + Z) '' integralOutside F r t A

theorem iUnion_cell (A : Finset (FinitePlace F)) (v : FinitePlace F) (hv : v ∉ A) :
    (⋃ y, cell r t A v y) = integralOutside F r t (Finset.cons v A hv) := by
  ext Y
  simp only [Set.mem_iUnion, cell, Set.mem_image]
  constructor
  · rintro ⟨y, Z, hZ, rfl⟩ w hw i j
    rw [Finset.mem_cons, not_or] at hw
    show matrixComponent w (localMatrix v (Quotient.out y) + Z) i j ∈ _
    rw [matrixComponent_add, matrixComponent_localMatrix_of_ne hw.1, zero_add]
    exact hZ w hw.2 i j
  · intro hY
    let y : LocalQuotient r t v := QuotientAddGroup.mk (matrixComponent v Y)
    refine ⟨y, Y - localMatrix v (Quotient.out y), fun w hw i j => ?_, add_sub_cancel _ _⟩
    show matrixComponent w (Y - localMatrix v (Quotient.out y)) i j ∈ _
    rw [matrixComponent_sub]
    by_cases hwv : w = v
    · subst hwv
      rw [matrixComponent_localMatrix]
      have hy : (QuotientAddGroup.mk (Quotient.out y) : LocalQuotient r t w) =
          QuotientAddGroup.mk (matrixComponent w Y) := Quotient.out_eq y
      rw [QuotientAddGroup.eq] at hy
      have h := (mem_integralMatrices_iff r t w _).1 hy i j
      have e : (matrixComponent w Y - Quotient.out y) i j =
          (-Quotient.out y + matrixComponent w Y) i j := by
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply]
        ring
      rw [e]
      exact h
    · rw [matrixComponent_localMatrix_of_ne hwv, sub_zero]
      exact hY w (by rw [Finset.mem_cons, not_or]; exact ⟨hwv, hw⟩) i j

theorem pairwise_disjoint_cell (A : Finset (FinitePlace F)) (v : FinitePlace F) (hv : v ∉ A) :
    Pairwise (Function.onFun Disjoint (cell r t A v)) := by
  intro y y' hyy'
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨Z, hZ, rfl⟩ ⟨Z', hZ', h⟩
  apply hyy'
  have hv' := congrArg (matrixComponent v) h
  rw [matrixComponent_add, matrixComponent_add, matrixComponent_localMatrix,
    matrixComponent_localMatrix] at hv'
  have hq : (QuotientAddGroup.mk (Quotient.out y) : LocalQuotient r t v) =
      QuotientAddGroup.mk (Quotient.out y') := by
    rw [QuotientAddGroup.eq, mem_integralMatrices_iff]
    intro i j
    have hij := congrFun (congrFun hv' i) j
    simp only [Matrix.add_apply] at hij
    have e : -Quotient.out y i j + Quotient.out y' i j =
        matrixComponent v Z i j - matrixComponent v Z' i j := by
      linear_combination hij
    show -Quotient.out y i j + Quotient.out y' i j ∈ _
    rw [e]
    exact (v.adicCompletionIntegers F).sub_mem (hZ v hv i j) (hZ' v hv i j)
  have e1 : (QuotientAddGroup.mk (Quotient.out y) : LocalQuotient r t v) = y := Quotient.out_eq y
  have e2 : (QuotientAddGroup.mk (Quotient.out y') : LocalQuotient r t v) = y' :=
    Quotient.out_eq y'
  rw [← e1, ← e2, hq]

end Integral

section Measure

variable {r t}

local instance matrixMeasurableSpace :
    MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
local instance matrixBorelSpace :
    BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩

theorem measurableSet_integralOutside (S : Finset (FinitePlace F)) :
    MeasurableSet (integralOutside F r t S) :=
  (isClosed_integralOutside r t S).measurableSet

theorem cell_eq_preimage (A : Finset (FinitePlace F)) (v : FinitePlace F)
    (y : LocalQuotient r t v) :
    cell r t A v y =
      (fun Y => -localMatrix v (Quotient.out y) + Y) ⁻¹' integralOutside F r t A := by
  ext Y
  simp only [cell, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    rwa [neg_add_cancel_left]
  · intro h
    exact ⟨_, h, add_neg_cancel_left _ _⟩

theorem measurableSet_cell (A : Finset (FinitePlace F)) (v : FinitePlace F)
    (y : LocalQuotient r t v) : MeasurableSet (cell r t A v y) := by
  rw [cell_eq_preimage]
  exact (measurable_const_add _) (measurableSet_integralOutside _)

variable (μ : Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))) [μ.IsAddLeftInvariant]

theorem setIntegral_cell (A : Finset (FinitePlace F)) (v : FinitePlace F)
    (y : LocalQuotient r t v) (f : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) → ℂ) :
    ∫ Y in cell r t A v y, f Y ∂μ =
      ∫ Z in integralOutside F r t A, f (localMatrix v (Quotient.out y) + Z) ∂μ :=
  (measurePreserving_add_left μ _).setIntegral_image_emb (measurableEmbedding_addLeft _) f _

/-- **One-place step.** Let `v ∉ A`. If `f` is integrable on the matrices integral outside
`A ∪ {v}`, and `f(y_v + Z) = c(y) f(Z)` for every class `y` of `M(F_v)/M(𝒪_v)` (with its
chosen representative placed at `v`) and every `Z` integral outside `A`, and `∑_y c(y) = L`,
then the integral over the matrices integral outside `A ∪ {v}` is `L` times the integral over
the matrices integral outside `A`. -/
theorem setIntegral_cons_eq_mul (A : Finset (FinitePlace F)) (v : FinitePlace F) (hv : v ∉ A)
    {f : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) → ℂ}
    (hf : IntegrableOn f (integralOutside F r t (Finset.cons v A hv)) μ)
    {c : LocalQuotient r t v → ℂ} {L : ℂ} (hc : HasSum c L)
    (hfac : ∀ y, ∀ Z ∈ integralOutside F r t A,
      f (localMatrix v (Quotient.out y) + Z) = c y * f Z) :
    ∫ Y in integralOutside F r t (Finset.cons v A hv), f Y ∂μ =
      L * ∫ Y in integralOutside F r t A, f Y ∂μ := by
  have h1 := hasSum_integral_iUnion (μ := μ) (f := f) (measurableSet_cell A v)
    (pairwise_disjoint_cell r t A v hv) (by rwa [iUnion_cell r t A v hv])
  rw [iUnion_cell r t A v hv] at h1
  have h2 : (fun y => ∫ Y in cell r t A v y, f Y ∂μ) =
      fun y => c y * ∫ Z in integralOutside F r t A, f Z ∂μ := by
    funext y
    rw [setIntegral_cell, ← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_integralOutside A) fun Z hZ => hfac y Z hZ
  rw [h2] at h1
  exact h1.unique (hc.mul_right _)

/-- Every adelic matrix is integral outside some finite set of finite places. -/
theorem exists_mem_integralOutside (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    ∃ A : Finset (FinitePlace F), Y ∈ integralOutside F r t A := by
  have hfin : ∀ i j, {v : FinitePlace F | matrixComponent v Y i j ∉ v.adicCompletionIntegers F}.Finite :=
    fun i j => Filter.eventually_cofinite.mp (Y i j).2.2
  have hU : (⋃ i, ⋃ j, {v : FinitePlace F |
      matrixComponent v Y i j ∉ v.adicCompletionIntegers F}).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j
  refine ⟨hU.toFinset, fun v hv i j => ?_⟩
  by_contra h
  exact hv (hU.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, h⟩⟩))

omit [μ.IsAddLeftInvariant] in
/-- **Exhaustion.** Let `f` be integrable on `M(𝔸)`. Suppose that adding a place `v ∉ A'` to
any finite `A' ⊇ S` multiplies the integral of `f` over the matrices integral outside `A'` by
`c_v`. If `∏_(v ∉ S) c_v` converges to `p`, then `∫ f = p · ∫_(U_S) f`. -/
theorem integral_eq_hasProd_mul_setIntegral (S : Finset (FinitePlace F))
    {f : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) → ℂ} (hf : Integrable f μ)
    {c : {v : FinitePlace F // v ∉ S} → ℂ} {p : ℂ} (hc : HasProd c p)
    (hstep : ∀ A : Finset (FinitePlace F), S ⊆ A → ∀ v : {v : FinitePlace F // v ∉ S},
      ∀ hv : v.1 ∉ A,
      ∫ Y in integralOutside F r t (Finset.cons v.1 A hv), f Y ∂μ =
        c v * ∫ Y in integralOutside F r t A, f Y ∂μ) :
    ∫ Y, f Y ∂μ = p * ∫ Y in integralOutside F r t S, f Y ∂μ := by
  classical
  have : Countable (FinitePlace F) := finitePlace_countable F
  let e : {v : FinitePlace F // v ∉ S} ↪ FinitePlace F := Function.Embedding.subtype _
  let s : Finset {v : FinitePlace F // v ∉ S} →
      Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := fun B =>
    integralOutside F r t (S ∪ B.map e)
  have hmono : Monotone s := fun B B' h =>
    integralOutside_mono r t (Finset.union_subset_union le_rfl (Finset.map_subset_map.mpr h))
  have hunion : (⋃ B, s B) = Set.univ := by
    refine Set.eq_univ_of_forall fun Y => ?_
    obtain ⟨A, hA⟩ := exists_mem_integralOutside (r := r) (t := t) Y
    refine Set.mem_iUnion.mpr ⟨A.subtype (fun v => v ∉ S), ?_⟩
    refine integralOutside_mono r t (fun v hv => ?_) hA
    by_cases hvS : v ∈ S
    · exact Finset.mem_union_left _ hvS
    · exact Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨⟨v, hvS⟩, Finset.mem_subtype.mpr hv, rfl⟩)
  have hprod : ∀ B : Finset {v : FinitePlace F // v ∉ S},
      ∫ Y in s B, f Y ∂μ = (∏ v ∈ B, c v) * ∫ Y in integralOutside F r t S, f Y ∂μ := by
    intro B
    induction B using Finset.induction_on with
    | empty => simp [s]
    | insert a B ha ih =>
      have hnot : a.1 ∉ S ∪ B.map e := by
        simp only [Finset.mem_union, Finset.mem_map, not_or, not_exists, not_and]
        exact ⟨a.2, fun b hb hba => ha (by
          have : b = a := Subtype.ext hba
          exact this ▸ hb)⟩
      have hins : S ∪ (insert a B).map e = Finset.cons a.1 (S ∪ B.map e) hnot := by
        rw [Finset.map_insert, Finset.union_insert, Finset.cons_eq_insert]
        rfl
      change ∫ Y in integralOutside F r t (S ∪ (insert a B).map e), f Y ∂μ = _
      rw [hins, hstep _ Finset.subset_union_left a hnot, Finset.prod_insert ha, mul_assoc]
      exact congrArg (c a * ·) ih
  have hlim1 : Filter.Tendsto (fun B => ∫ Y in s B, f Y ∂μ) Filter.atTop
      (nhds (∫ Y, f Y ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone
      (fun B => measurableSet_integralOutside (r := r) (t := t) _) hmono hf.integrableOn
    rwa [hunion, Measure.restrict_univ] at h
  have hlim2 : Filter.Tendsto (fun B => ∫ Y in s B, f Y ∂μ) Filter.atTop
      (nhds (p * ∫ Y in integralOutside F r t S, f Y ∂μ)) := by
    have hc' : Filter.Tendsto (fun B : Finset {v : FinitePlace F // v ∉ S} => ∏ v ∈ B, c v)
        Filter.atTop (nhds p) := hc
    simp_rw [hprod]
    exact hc'.mul_const _
  exact tendsto_nhds_unique hlim1 hlim2

end Measure

end Langlands.Global.CuspidalPairEisenstein.OpenCellExhaustion
