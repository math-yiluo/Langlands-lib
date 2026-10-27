import Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Tensor.FiniteProperties
import Mathlib.GroupTheory.DoubleCoset

/-!
# Bijectivity of the finite-product induction tensor map

For a finite family of subgroups `P i ≤ G i` with compact coset spaces over
weakly locally compact nonarchimedean groups, the canonical pointwise map
`finiteProductTensorMap P σ` is bijective over a field. At a compact open level
`K i`, every factor function is a finite sum of double-coset sections, one for
each class of `P i \ G i / K i`; tensoring these sections gives the inverse
construction.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Induction

universe uK uI uG uV

namespace FiniteProductTensorBijective

section Factor

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module k V]
variable (P : Subgroup G) (σ : Representation k P V)

omit [IsTopologicalGroup G] in
/-- Smooth induced functions are determined by their values. -/
theorem smoothFunctions_ext {f h : SmoothFunctions P σ}
    (H : ∀ y, eval P σ f y = eval P σ h y) : f = h :=
  Subtype.ext (Subtype.ext (funext H))

/-- Evaluation at a point, as a linear map. -/
def evalLinear (y : G) : SmoothFunctions P σ →ₗ[k] V where
  toFun f := eval P σ f y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] in
theorem eval_zero (y : G) : eval P σ 0 y = 0 := rfl

omit [IsTopologicalGroup G] in
theorem eval_sum {α : Type*} (s : Finset α) (F : α → SmoothFunctions P σ) (y : G) :
    eval P σ (∑ a ∈ s, F a) y = ∑ a ∈ s, eval P σ (F a) y :=
  map_sum (evalLinear P σ y) F s

variable (K : OpenSubgroup G)

/-- The class of `y` in the double-coset space `P \ G / K`. -/
abbrev doubleClass (y : G) : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G) :=
  DoubleCoset.mk P K.toSubgroup y

/-- A compact coset space has finitely many double cosets for an open subgroup. -/
theorem finite_doubleCosetQuotient [CompactSpace (LeftQuotient P)] :
    Finite (DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G)) := by
  obtain ⟨t, ht⟩ := exists_finset_doubleCoset_cover P K
  refine Finite.of_surjective (fun x : t => doubleClass P K (x : G)) (fun q => ?_)
  obtain ⟨i, hi, p, hp, l, hl, he⟩ := ht q.out
  exact ⟨⟨i, hi⟩, (DoubleCoset.eq.mpr ⟨p, hp, l, hl, he⟩).trans (DoubleCoset.out_eq' q)⟩

variable (hK : IsCompact (K : Set G))

/-- The double-coset section at `a * x * b`. -/
theorem section_eval_mul (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    {a b : G} (ha : a ∈ P) (hb : b ∈ K) :
    eval P σ (compactDoubleCosetSection P σ K hK x v hv).val (a * x * b) = σ ⟨a, ha⟩ v :=
  compactDoubleCosetSection_apply P σ K hK x v hv ⟨a, ha⟩ ⟨b, hb⟩

/-- The double-coset section vanishes outside the double coset `P * x * K`. -/
theorem section_eval_of_ne (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) {y : G}
    (hy : doubleClass P K y ≠ doubleClass P K x) :
    eval P σ (compactDoubleCosetSection P σ K hK x v hv).val y = 0 := by
  by_contra h
  obtain ⟨l, hl, he⟩ :=
    compactDoubleCosetSection_support_subset P σ K hK x v hv ⟨y, h, rfl⟩
  have hp : y * (x * l)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  exact hy (DoubleCoset.eq.mpr
    ⟨(y * (x * l)⁻¹)⁻¹, P.inv_mem hp, l⁻¹, K.inv_mem hl, by group⟩)

/-- The double-coset section construction as a linear map on the fixed
coefficient space of `x`. -/
def sectionMap (x : G) :
    fixedVectors σ (conjOpenSubgroup P K x).toSubgroup →ₗ[k] SmoothFunctions P σ where
  toFun v := (compactDoubleCosetSection P σ K hK x v.1 v.2).val
  map_add' v w := by
    refine smoothFunctions_ext P σ (fun y => ?_)
    change _ = eval P σ (compactDoubleCosetSection P σ K hK x v.1 v.2).val y +
      eval P σ (compactDoubleCosetSection P σ K hK x w.1 w.2).val y
    by_cases h : doubleClass P K x = doubleClass P K y
    · obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
      rw [section_eval_mul P σ K hK x _ _ ha hb, section_eval_mul P σ K hK x _ _ ha hb,
        section_eval_mul P σ K hK x _ _ ha hb, Submodule.coe_add, map_add]
    · have h' : doubleClass P K y ≠ doubleClass P K x := Ne.symm h
      rw [section_eval_of_ne P σ K hK x _ _ h', section_eval_of_ne P σ K hK x _ _ h',
        section_eval_of_ne P σ K hK x _ _ h', add_zero]
  map_smul' c v := by
    refine smoothFunctions_ext P σ (fun y => ?_)
    change _ = c • eval P σ (compactDoubleCosetSection P σ K hK x v.1 v.2).val y
    by_cases h : doubleClass P K x = doubleClass P K y
    · obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
      rw [section_eval_mul P σ K hK x _ _ ha hb, section_eval_mul P σ K hK x _ _ ha hb,
        Submodule.coe_smul, map_smul]
    · have h' : doubleClass P K y ≠ doubleClass P K x := Ne.symm h
      rw [section_eval_of_ne P σ K hK x _ _ h', section_eval_of_ne P σ K hK x _ _ h',
        smul_zero]

/-- Evaluation of a `K`-fixed function at `x`, valued in the fixed coefficient
space of `x`. -/
def pointEvaluation (x : G) :
    fixedVectors (smoothInduced P σ) K.toSubgroup →ₗ[k]
      fixedVectors σ (conjOpenSubgroup P K x).toSubgroup where
  toFun f := ⟨eval P σ f.1 x, eval_mem_fixedVectors P σ K x f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A `K`-fixed function is the sum of the sections through its values at
representatives of the distinct double cosets. -/
theorem subtype_eq_sum
    [Fintype (DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G))] :
    (fixedVectors (smoothInduced P σ) K.toSubgroup).subtype =
      ∑ q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G),
        sectionMap P σ K hK q.out ∘ₗ pointEvaluation P σ K q.out := by
  classical
  refine LinearMap.ext (fun f => smoothFunctions_ext P σ (fun y => ?_))
  rw [LinearMap.sum_apply, eval_sum, Finset.sum_eq_single (doubleClass P K y)]
  · obtain ⟨a, ha, b, hb, hy⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' (doubleClass P K y))
    rw [LinearMap.comp_apply]
    set x := (doubleClass P K y).out
    calc eval P σ ((fixedVectors (smoothInduced P σ) K.toSubgroup).subtype f) y
        = eval P σ f.1 (a * x * b) := congrArg (eval P σ f.1) hy
      _ = σ ⟨a, ha⟩ (eval P σ f.1 x) := by
        rw [eval_mul_of_mem_fixedVectors P σ K.toSubgroup f.2 ⟨b, hb⟩,
          eval_covariant P σ f.1 ⟨a, ha⟩]
      _ = eval P σ (sectionMap P σ K hK x (pointEvaluation P σ K x f)) (a * x * b) :=
        (section_eval_mul P σ K hK x (pointEvaluation P σ K x f).1
          (pointEvaluation P σ K x f).2 ha hb).symm
      _ = eval P σ (sectionMap P σ K hK x (pointEvaluation P σ K x f)) y :=
        congrArg (eval P σ _) hy.symm
  · intro q _ hq
    rw [LinearMap.comp_apply]
    refine section_eval_of_ne P σ K hK _ (pointEvaluation P σ K q.out f).1
      (pointEvaluation P σ K q.out f).2 (fun h => ?_)
    exact hq ((DoubleCoset.out_eq' q).symm.trans h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

end Factor

section Product

variable {k : Type uK} [Field k] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (P : ∀ i, Subgroup (G i)) (σ : ∀ i, Representation k (P i) (V i))
variable (K : ∀ i, OpenSubgroup (G i))

/-- The tensor product of the factor section maps at a tuple `x`. -/
def productSection (hK : ∀ i, IsCompact (K i : Set (G i))) (x : ∀ i, G i) :
    (⨂[k] i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup) →ₗ[k]
      ⨂[k] i, SmoothFunctions (P i) (σ i) :=
  PiTensorProduct.map (fun i => sectionMap (P i) (σ i) (K i) (hK i) (x i))

/-- The inclusion of the tensor of fixed coefficient spaces in the inducing tensor. -/
def coefficientInclusion (x : ∀ i, G i) :
    (⨂[k] i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup) →ₗ[k]
      ⨂[k] i, V i :=
  PiTensorProduct.map (fun i =>
    (fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup).subtype)

omit [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
/-- Over a field, the tensor product of submodule inclusions is injective. -/
theorem map_subtype_injective (W : ∀ i, Submodule k (V i)) :
    Function.Injective (PiTensorProduct.map (fun i => (W i).subtype)) := by
  have hcompl : ∀ i, ∃ C : Submodule k (V i), IsCompl (W i) C :=
    fun i => Submodule.exists_isCompl _
  choose C hC using hcompl
  refine Function.LeftInverse.injective
    (g := PiTensorProduct.map (fun i => Submodule.projectionOnto (W i) (C i) (hC i))) ?_
  intro t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have h : (fun i => Submodule.projectionOnto (W i) (C i) (hC i) ∘ₗ (W i).subtype) =
      fun i => LinearMap.id := by
    funext i
    ext v
    simp
  rw [h, PiTensorProduct.map_id, LinearMap.id_apply]

variable (hK : ∀ i, IsCompact (K i : Set (G i)))

/-- The image of a tensor of sections, evaluated in the product double coset of `x`. -/
theorem eval_productSection [Finite ι] (x : ∀ i, G i)
    (t : ⨂[k] i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup)
    (p : Subgroup.pi Set.univ P) {b : ∀ i, G i} (hb : ∀ i, b i ∈ K i) :
    eval (Subgroup.pi Set.univ P) (productInducing P σ)
        (finiteProductTensorMap P σ (productSection P σ K hK x t))
        ((p : ∀ i, G i) * x * b) =
      productInducing P σ p (coefficientInclusion P σ K x t) := by
  have h : evalLinear (Subgroup.pi Set.univ P) (productInducing P σ)
        ((p : ∀ i, G i) * x * b) ∘ₗ (finiteProductTensorMap P σ).toLinearMap ∘ₗ
          productSection P σ K hK x =
      (productInducing P σ p) ∘ₗ coefficientInclusion P σ K x := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, productSection,
      coefficientInclusion, PiTensorProduct.map_tprod, productInducing_tprod,
      Submodule.subtype_apply]
    change eval _ _ (finiteProductTensorMap P σ (PiTensorProduct.tprod k _)) _ = _
    rw [finiteProductTensorMap_tprod_eval]
    congr 1
    funext i
    exact section_eval_mul (P i) (σ i) (K i) (hK i) (x i) (w i).1 (w i).2
      (p.2 i (Set.mem_univ i)) (hb i)
  exact LinearMap.congr_fun h t

/-- The image of a tensor of sections, evaluated at `x` itself. -/
theorem eval_productSection_self [Finite ι] (x : ∀ i, G i)
    (t : ⨂[k] i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup) :
    eval (Subgroup.pi Set.univ P) (productInducing P σ)
        (finiteProductTensorMap P σ (productSection P σ K hK x t)) x =
      coefficientInclusion P σ K x t := by
  have h := eval_productSection P σ K hK x t 1 (b := 1) (fun i => (K i).one_mem)
  simpa only [OneMemClass.coe_one, one_mul, mul_one, map_one, Module.End.one_apply] using h

/-- The image of a tensor of sections vanishes off the product double coset of `x`. -/
theorem eval_productSection_of_ne [Finite ι] (x : ∀ i, G i)
    (t : ⨂[k] i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup)
    {g : ∀ i, G i} (j : ι)
    (hj : doubleClass (P j) (K j) (g j) ≠ doubleClass (P j) (K j) (x j)) :
    eval (Subgroup.pi Set.univ P) (productInducing P σ)
        (finiteProductTensorMap P σ (productSection P σ K hK x t)) g = 0 := by
  have h : evalLinear (Subgroup.pi Set.univ P) (productInducing P σ) g ∘ₗ
        (finiteProductTensorMap P σ).toLinearMap ∘ₗ productSection P σ K hK x = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, productSection,
      PiTensorProduct.map_tprod, LinearMap.zero_compMultilinearMap,
      zero_apply]
    change eval _ _ (finiteProductTensorMap P σ (PiTensorProduct.tprod k _)) _ = 0
    rw [finiteProductTensorMap_tprod_eval]
    exact MultilinearMap.map_coord_zero _ j
      (section_eval_of_ne (P j) (σ j) (K j) (hK j) (x j) (w j).1 (w j).2 hj)
  exact LinearMap.congr_fun h t

omit [∀ i, IsTopologicalGroup (G i)] in
/-- A point whose coordinates lie in the double cosets of `x` factors as `p * x * b`. -/
theorem exists_decomposition (g x : ∀ i, G i)
    (hx : ∀ i, DoubleCoset.mk (P i) (K i).toSubgroup (x i) =
      DoubleCoset.mk (P i) (K i).toSubgroup (g i)) :
    ∃ p : Subgroup.pi Set.univ P, ∃ b : ∀ i, G i, (∀ i, b i ∈ K i) ∧
      g = (p : ∀ i, G i) * x * b := by
  choose a ha c hc he using fun i => DoubleCoset.eq.mp (hx i)
  exact ⟨⟨a, fun i _ => ha i⟩, c, hc, funext he⟩

/-- A product-level invariant function has coefficient values fixed by the
product of the conjugate-intersection subgroups. -/
theorem eval_mem_fixedVectors_pi [Finite ι]
    (F : SmoothFunctions (Subgroup.pi Set.univ P) (productInducing P σ))
    (hF : ∀ b : ∀ i, G i, (∀ i, b i ∈ K i) → ∀ y,
      eval _ _ F (y * b) = eval _ _ F y) (x : ∀ i, G i) :
    eval _ _ F x ∈ fixedVectors (FiniteTensor.external σ)
      (Subgroup.pi Set.univ (fun i => (conjOpenSubgroup (P i) (K i) (x i)).toSubgroup)) := by
  rintro ⟨a, ha⟩
  let p : Subgroup.pi Set.univ P := ⟨fun i => (a i : G i), fun i _ => (a i).2⟩
  have hb : ∀ i, (x⁻¹ * (p : ∀ i, G i) * x) i ∈ K i :=
    fun i => mem_conjOpenSubgroup.mp (ha i (Set.mem_univ i))
  change productInducing P σ p (eval _ _ F x) = eval _ _ F x
  rw [← eval_covariant]
  calc eval _ _ F ((p : ∀ i, G i) * x)
      = eval _ _ F (x * (x⁻¹ * (p : ∀ i, G i) * x)) := by group
    _ = eval _ _ F x := hF _ hb x

end Product

section Main

variable {k : Type uK} [Field k] {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, NonarchimedeanGroup (G i)] [∀ i, WeaklyLocallyCompactSpace (G i)]
variable {P : ∀ i, Subgroup (G i)} [∀ i, CompactSpace (LeftQuotient (P i))]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (σ : ∀ i, Representation k (P i) (V i))

omit [Fintype ι] [DecidableEq ι] in
/-- Every family of open subgroups contains a family of compact open subgroups. -/
theorem exists_compact_level (L : ∀ i, OpenSubgroup (G i)) :
    ∃ K : ∀ i, OpenSubgroup (G i), (∀ i, IsCompact (K i : Set (G i))) ∧
      ∀ i, (K i : Set (G i)) ⊆ L i := by
  have h : ∀ i, ∃ K : OpenSubgroup (G i), IsCompact (K : Set (G i)) ∧
      (K : Set (G i)) ⊆ L i := fun i =>
    compactOpenSubgroupBasis (G i) (L i : Set (G i)) ((L i).isOpen.mem_nhds (L i).one_mem)
  choose K hK hKL using h
  exact ⟨K, hK, hKL⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, WeaklyLocallyCompactSpace (G i)]
  [∀ i, CompactSpace (LeftQuotient (P i))] in
/-- Shrinking the levels enlarges the range of the tensor of fixed-vector inclusions. -/
theorem range_map_fixed_mono {L M : ∀ i, OpenSubgroup (G i)}
    (h : ∀ i, (M i : Set (G i)) ⊆ L i) :
    LinearMap.range (PiTensorProduct.map (fun i =>
        (fixedVectors (smoothInduced (P i) (σ i)) (L i).toSubgroup).subtype)) ≤
      LinearMap.range (PiTensorProduct.map (fun i =>
        (fixedVectors (smoothInduced (P i) (σ i)) (M i).toSubgroup).subtype)) := by
  have hle : ∀ i, fixedVectors (smoothInduced (P i) (σ i)) (L i).toSubgroup ≤
      fixedVectors (smoothInduced (P i) (σ i)) (M i).toSubgroup :=
    fun i v hv g => hv ⟨g.1, h i g.2⟩
  have he : PiTensorProduct.map (fun i =>
        (fixedVectors (smoothInduced (P i) (σ i)) (L i).toSubgroup).subtype) =
      PiTensorProduct.map (fun i =>
        (fixedVectors (smoothInduced (P i) (σ i)) (M i).toSubgroup).subtype) ∘ₗ
      PiTensorProduct.map (fun i => Submodule.inclusion (hle i)) := by
    rw [← PiTensorProduct.map_comp]
    rfl
  rw [he]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype ι] [DecidableEq ι] [∀ i, WeaklyLocallyCompactSpace (G i)]
  [∀ i, CompactSpace (LeftQuotient (P i))] in
/-- Every tensor of smooth induced functions comes from fixed vectors at one level. -/
theorem exists_level (z : ⨂[k] i, SmoothFunctions (P i) (σ i)) :
    ∃ L : ∀ i, OpenSubgroup (G i), z ∈ LinearMap.range (PiTensorProduct.map (fun i =>
      (fixedVectors (smoothInduced (P i) (σ i)) (L i).toSubgroup).subtype)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h : ∀ i, ∃ L : OpenSubgroup (G i),
        f i ∈ fixedVectors (smoothInduced (P i) (σ i)) L.toSubgroup :=
      fun i => smoothInduced_smooth (P i) (σ i) (f i)
    choose L hL using h
    refine ⟨L, r • PiTensorProduct.tprod k (fun i => ⟨f i, hL i⟩), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add z w hz hw =>
    obtain ⟨L, hLz⟩ := hz
    obtain ⟨M, hMw⟩ := hw
    refine ⟨fun i => L i ⊓ M i, add_mem ?_ ?_⟩
    · exact range_map_fixed_mono σ (fun i => inf_le_left (a := L i) (b := M i)) hLz
    · exact range_map_fixed_mono σ (fun i => inf_le_right (a := L i) (b := M i)) hMw

/-- Surjectivity of the canonical finite-product tensor map. -/
theorem finiteProductTensorMap_surjective :
    Function.Surjective (finiteProductTensorMap P σ) := by
  classical
  intro F
  obtain ⟨L, hL⟩ := smoothInduced_smooth (Subgroup.pi Set.univ P) (productInducing P σ) F
  obtain ⟨K, hK, hKL⟩ := exists_compact_level
    (fun i => L.comap (MonoidHom.mulSingle G i) (continuous_mulSingle i))
  have hF : ∀ b : ∀ i, G i, (∀ i, b i ∈ K i) → ∀ y,
      eval _ _ F (y * b) = eval _ _ F y := fun b hb y =>
    eval_mul_of_mem_fixedVectors _ _ L.toSubgroup hL
      ⟨b, Subgroup.pi_mem_of_mulSingle_mem b (fun i => hKL i (hb i))⟩ y
  have : ∀ i, Finite (DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i))) :=
    fun i => finite_doubleCosetQuotient (P i) (K i)
  have : ∀ i, Fintype (DoubleCoset.Quotient (P i : Set (G i))
      ((K i).toSubgroup : Set (G i))) := fun i => Fintype.ofFinite _
  let rep : (∀ i, DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i))) →
      ∀ i, G i := fun q i => (q i).out
  have hcoef : ∀ q, eval _ _ F (rep q) ∈ LinearMap.range (coefficientInclusion P σ K (rep q)) :=
    fun q => FiniteTensor.fixedVectors_external_le σ _
      (eval_mem_fixedVectors_pi P σ K F hF (rep q))
  choose t ht using hcoef
  refine ⟨∑ q, productSection P σ K hK (rep q) (t q), ?_⟩
  refine smoothFunctions_ext _ _ (fun g => ?_)
  obtain ⟨q0, hq0⟩ : ∃ q0 : ∀ i, DoubleCoset.Quotient (P i : Set (G i))
      ((K i).toSubgroup : Set (G i)), q0 = fun i => doubleClass (P i) (K i) (g i) := ⟨_, rfl⟩
  rw [map_sum, eval_sum, Finset.sum_eq_single q0]
  · obtain ⟨p, b, hb, hg⟩ := exists_decomposition P K g (rep q0)
      (fun i => by rw [hq0]; exact DoubleCoset.out_eq' _)
    calc eval _ _ (finiteProductTensorMap P σ (productSection P σ K hK (rep q0) (t q0))) g
        = eval _ _ (finiteProductTensorMap P σ (productSection P σ K hK (rep q0) (t q0)))
            ((p : ∀ i, G i) * rep q0 * b) := congrArg (eval _ _ _) hg
      _ = productInducing P σ p (coefficientInclusion P σ K (rep q0) (t q0)) :=
        eval_productSection P σ K hK (rep q0) (t q0) p hb
      _ = productInducing P σ p (eval _ _ F (rep q0)) := by rw [ht]
      _ = eval _ _ F ((p : ∀ i, G i) * rep q0) := (eval_covariant _ _ F p (rep q0)).symm
      _ = eval _ _ F ((p : ∀ i, G i) * rep q0 * b) := (hF b hb _).symm
      _ = eval _ _ F g := congrArg (eval _ _ F) hg.symm
  · intro q _ hq
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hq
    apply eval_productSection_of_ne P σ K hK (rep q) (t q) j
    intro h
    exact hj (((DoubleCoset.out_eq' (q j)).symm.trans h.symm).trans (congrFun hq0 j).symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Injectivity of the canonical finite-product tensor map. -/
theorem finiteProductTensorMap_injective :
    Function.Injective (finiteProductTensorMap P σ) := by
  classical
  refine (injective_iff_map_eq_zero (finiteProductTensorMap P σ)).mpr (fun z hz => ?_)
  obtain ⟨L, hL⟩ := exists_level σ z
  obtain ⟨K, hK, hKL⟩ := exists_compact_level L
  obtain ⟨y, rfl⟩ := range_map_fixed_mono σ hKL hL
  have : ∀ i, Finite (DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i))) :=
    fun i => finite_doubleCosetQuotient (P i) (K i)
  have : ∀ i, Fintype (DoubleCoset.Quotient (P i : Set (G i))
      ((K i).toSubgroup : Set (G i))) := fun i => Fintype.ofFinite _
  let rep : (∀ i, DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i))) →
      ∀ i, G i := fun q i => (q i).out
  have hexp : PiTensorProduct.map (fun i =>
        (fixedVectors (smoothInduced (P i) (σ i)) (K i).toSubgroup).subtype) =
      ∑ q, productSection P σ K hK (rep q) ∘ₗ
        PiTensorProduct.map (fun i => pointEvaluation (P i) (σ i) (K i) (rep q i)) := by
    have h := (PiTensorProduct.mapMultilinear k
      (fun i => fixedVectors (smoothInduced (P i) (σ i)) (K i).toSubgroup)
      (fun i => SmoothFunctions (P i) (σ i))).map_sum
      (fun i (q : DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i))) =>
        sectionMap (P i) (σ i) (K i) (hK i) q.out ∘ₗ pointEvaluation (P i) (σ i) (K i) q.out)
    simp only [PiTensorProduct.mapMultilinear_apply] at h
    rw [show (fun i => (fixedVectors (smoothInduced (P i) (σ i)) (K i).toSubgroup).subtype) =
        fun i => ∑ q : DoubleCoset.Quotient (P i : Set (G i)) ((K i).toSubgroup : Set (G i)),
          sectionMap (P i) (σ i) (K i) (hK i) q.out ∘ₗ
            pointEvaluation (P i) (σ i) (K i) q.out from
      funext fun i => subtype_eq_sum (P i) (σ i) (K i) (hK i), h]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [PiTensorProduct.map_comp]
    rfl
  rw [hexp, LinearMap.sum_apply] at hz ⊢
  have hu : ∀ q0, PiTensorProduct.map
      (fun i => pointEvaluation (P i) (σ i) (K i) (rep q0 i)) y = 0 := by
    intro q0
    apply map_subtype_injective
    rw [map_zero]
    have h := congrArg (fun F => eval _ _ F (rep q0)) hz
    simp only [eval_zero] at h
    rw [map_sum, eval_sum, Finset.sum_eq_single q0] at h
    · rw [LinearMap.comp_apply, eval_productSection_self] at h
      exact h
    · intro q _ hq
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hq
      rw [LinearMap.comp_apply]
      apply eval_productSection_of_ne P σ K hK (rep q) _ j
      intro h
      exact hj ((DoubleCoset.out_eq' (q j)).symm.trans
        (h.symm.trans (DoubleCoset.out_eq' (q0 j))))
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact Finset.sum_eq_zero (fun q _ => by rw [LinearMap.comp_apply, hu q, map_zero])

end Main

end FiniteProductTensorBijective

open FiniteProductTensorBijective in
/-- The canonical finite-product induction tensor map is bijective. -/
theorem finiteProductTensorMap_bijective :
    FiniteProductTensorBijectiveTheorem.{uK, uI, uG, uV} := by
  intro k _ ι _ G _ _ _ _ P _ V _ _ σ
  classical
  let _ := Fintype.ofFinite ι
  exact ⟨finiteProductTensorMap_injective σ, finiteProductTensorMap_surjective σ⟩

end Langlands.Induction
