import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Twist.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Basic.Complex.Basic

/-!
# Grading compact induction by an open normal subgroup

Let `ν : G →* D` be a homomorphism to a commutative group with open kernel, and let `P` be a
subgroup contained in that kernel. A compactly induced function `f ∈ c-Ind_P^G σ` splits into
finitely many pieces `f_d`, where `f_d` agrees with `f` on `ν⁻¹(d)` and vanishes elsewhere.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open Langlands.Induction

universe uG uV uW uD

section Grading

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {D : Type uD} [CommGroup D] [DecidableEq D]
  {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ P V}
  (ν : G →* D)

/-- The kernel of `ν` as an open subgroup. -/
def kerOpenSubgroup (hν : IsOpen (ν.ker : Set G)) : OpenSubgroup G :=
  { toSubgroup := ν.ker
    isOpen' := hν }

theorem isLocallyConstant_of_isOpen_ker (hν : IsOpen (ν.ker : Set G)) :
    IsLocallyConstant ν := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (ν.ker : Set G), isOpenMap_mul_left x _ hν,
    ⟨1, ν.ker.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]

/-- A smooth covariant function is locally constant. -/
theorem isLocallyConstant_eval (f : SmoothFunctions P σ) :
    IsLocallyConstant (eval P σ f) := by
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set G),
    isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (fun F : EquivariantFunctions P σ => F.1 x) (hK ⟨k, hk⟩)

/-- The quotient support of a smooth covariant function is closed. -/
theorem isClosed_quotientSupport (f : SmoothFunctions P σ) :
    IsClosed (quotientSupport P (eval P σ f)) := by
  have hpre : quotientMap P ⁻¹' quotientSupport P (eval P σ f) =
      Function.support (eval P σ f) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      intro hx
      have hp : y * x⁻¹ ∈ P :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
      have hf : eval P σ f ((⟨y * x⁻¹, hp⟩ : P) * x) = σ ⟨y * x⁻¹, hp⟩ (eval P σ f x) :=
        f.1.property ⟨y * x⁻¹, hp⟩ x
      rw [hx, map_zero] at hf
      apply hy
      simpa [mul_assoc] using hf
    · intro hx
      exact ⟨x, hx, rfl⟩
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
  change IsClosed (quotientMap P ⁻¹' quotientSupport P (eval P σ f))
  rw [hpre]
  exact ((isLocallyConstant_eval f).isOpen_fiber 0).isClosed_compl

variable {ν}

/-- The function-level graded piece of degree `d`. -/
def gradedFun (d : D) (f : G → V) : G → V :=
  fun g => if ν g = d then f g else 0

theorem gradedFun_apply (d : D) (f : G → V) (g : G) :
    gradedFun (ν := ν) d f g = if ν g = d then f g else 0 := rfl

variable (hP : P ≤ ν.ker) (hν : IsOpen (ν.ker : Set G))
include hP hν

/-- The graded piece of a smooth induced function. -/
def gradedSmooth (d : D) (f : SmoothFunctions P σ) : SmoothFunctions P σ :=
  smoothFunctionOf P σ (gradedFun (ν := ν) d (eval P σ f))
    (by
      intro p x
      have hpx : ν ((p : G) * x) = ν x := by
        rw [map_mul, MonoidHom.mem_ker.mp (hP p.property), one_mul]
      simp only [gradedFun_apply, hpx]
      split_ifs
      · exact f.1.property p x
      · exact (map_zero (σ p)).symm)
    (Classical.choose f.property ⊓ kerOpenSubgroup ν hν)
    (by
      intro k x
      have hk := (Classical.choose_spec f.property) ⟨k.val, k.property.1⟩
      have hxk : ν (x * (k : G)) = ν x := by
        rw [map_mul, MonoidHom.mem_ker.mp k.property.2, mul_one]
      simp only [gradedFun_apply, hxk]
      split_ifs
      · exact congrArg (fun F : EquivariantFunctions P σ => F.1 x) hk
      · rfl)

theorem eval_gradedSmooth (d : D) (f : SmoothFunctions P σ) (g : G) :
    eval P σ (gradedSmooth hP hν d f) g = if ν g = d then eval P σ f g else 0 := rfl

/-- The graded piece of a compactly induced function. -/
def gradedPiece (d : D) (f : CompactFunctions P σ) : CompactFunctions P σ :=
  ⟨gradedSmooth hP hν d f.1, by
    apply f.2.of_isClosed_subset (isClosed_quotientSupport _)
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    intro h0
    apply hx
    rw [eval_gradedSmooth]
    split_ifs
    · exact h0
    · rfl⟩

theorem eval_gradedPiece (d : D) (f : CompactFunctions P σ) (g : G) :
    eval P σ (gradedPiece hP hν d f).1 g = if ν g = d then eval P σ f.1 g else 0 := rfl

omit hP hν in
theorem compactFunctions_ext {f h : CompactFunctions P σ}
    (H : ∀ g, eval P σ f.1 g = eval P σ h.1 g) : f = h :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext H)))

omit hP hν in
@[simp] theorem eval_add (f h : CompactFunctions P σ) (g : G) :
    eval P σ (f + h).1 g = eval P σ f.1 g + eval P σ h.1 g := rfl

omit hP hν in
@[simp] theorem eval_smul (a : ℂ) (f : CompactFunctions P σ) (g : G) :
    eval P σ (a • f).1 g = a • eval P σ f.1 g := rfl

omit hP hν in
@[simp] theorem eval_zero (g : G) :
    eval P σ (0 : CompactFunctions P σ).1 g = 0 := rfl

omit hP hν in
@[simp] theorem eval_translate (f : CompactFunctions P σ) (s g : G) :
    eval P σ (compactInduced P σ s f).1 g = eval P σ f.1 (g * s) := rfl

omit [DecidableEq D] in
/-- Evaluation at a point as a linear map on compactly induced functions. -/
def evalLinear (g : G) : CompactFunctions P σ →ₗ[ℂ] V where
  toFun f := eval P σ f.1 g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit hP hν in
@[simp] theorem eval_sum {ι : Type*} (t : Finset ι) (f : ι → CompactFunctions P σ) (g : G) :
    eval P σ (∑ i ∈ t, f i).1 g = ∑ i ∈ t, eval P σ (f i).1 g :=
  map_sum (evalLinear (P := P) (σ := σ) g) f t

/-- The graded piece as a linear map. -/
def gradedProjection (d : D) : CompactFunctions P σ →ₗ[ℂ] CompactFunctions P σ where
  toFun := gradedPiece hP hν d
  map_add' f h := by
    apply compactFunctions_ext
    intro g
    simp only [eval_gradedPiece, eval_add]
    split_ifs <;> simp
  map_smul' a f := by
    apply compactFunctions_ext
    intro g
    simp only [eval_gradedPiece, eval_smul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem gradedProjection_apply (d : D) (f : CompactFunctions P σ) :
    gradedProjection hP hν d f = gradedPiece hP hν d f := rfl

/-- Translation shifts the degree. -/
theorem gradedPiece_translate (d : D) (s : G) (f : CompactFunctions P σ) :
    gradedPiece hP hν d (compactInduced P σ s f) =
      compactInduced P σ s (gradedPiece hP hν (d * ν s) f) := by
  apply compactFunctions_ext
  intro g
  simp only [eval_gradedPiece, eval_translate, map_mul]
  by_cases h : ν g = d
  · simp [h]
  · have h' : ¬ ν g * ν s = d * ν s := fun h'' => h (mul_right_cancel h'')
    simp [h, h']

/-- Elements of the kernel commute with the graded pieces. -/
theorem gradedPiece_translate_ker (d : D) {s : G} (hs : s ∈ ν.ker) (f : CompactFunctions P σ) :
    gradedPiece hP hν d (compactInduced P σ s f) =
      compactInduced P σ s (gradedPiece hP hν d f) := by
  rw [gradedPiece_translate, MonoidHom.mem_ker.mp hs, mul_one]

/-- The degrees occurring in a compactly induced function. -/
def degreeSet (ν : G →* D) (f : CompactFunctions P σ) : Set D :=
  ν '' Function.support (eval P σ f.1)

theorem degreeSet_finite (f : CompactFunctions P σ) : (degreeSet ν f).Finite := by
  let νbar : LeftQuotient P → D :=
    Quotient.lift ν (by
      intro a b hab
      have : b * a⁻¹ ∈ ν.ker := hP (QuotientGroup.rightRel_apply.mp hab)
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
      exact this.symm)
  have hlc : IsLocallyConstant νbar := by
    apply (IsLocallyConstant.iff_isOpen_fiber).mpr
    intro d
    apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isOpen_preimage.mp
    exact (isLocallyConstant_of_isOpen_ker ν hν).isOpen_fiber d
  have himage : degreeSet ν f = νbar '' quotientSupport P (eval P σ f.1) := by
    ext d
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨quotientMap P g, ⟨g, hg, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [himage]
  have hK : IsCompact (quotientSupport P (eval P σ f.1)) := f.2
  have : CompactSpace (quotientSupport P (eval P σ f.1)) := isCompact_iff_compactSpace.mp hK
  have hfin := (hlc.comp_continuous
    (continuous_subtype_val (p := (· ∈ quotientSupport P (eval P σ f.1))))).range_finite
  convert hfin using 1
  ext d
  simp [Set.mem_image, Set.mem_range]

/-- A graded piece outside the degree set vanishes. -/
theorem gradedPiece_eq_zero_of_notMem {d : D} (f : CompactFunctions P σ)
    (hd : d ∉ degreeSet ν f) : gradedPiece hP hν d f = 0 := by
  apply compactFunctions_ext
  intro g
  rw [eval_gradedPiece, eval_zero]
  split_ifs with h
  · by_contra hne
    exact hd ⟨g, hne, h⟩
  · rfl

/-- A compactly induced function is the sum of its graded pieces. -/
theorem sum_gradedPiece (f : CompactFunctions P σ) :
    ∑ d ∈ (degreeSet_finite hP hν f).toFinset, gradedPiece hP hν d f = f := by
  apply compactFunctions_ext
  intro g
  rw [eval_sum]
  by_cases hg : eval P σ f.1 g = 0
  · rw [hg]
    apply Finset.sum_eq_zero
    intro d _
    rw [eval_gradedPiece, hg]
    simp
  · rw [Finset.sum_eq_single (ν g)]
    · simp [eval_gradedPiece]
    · intro d _ hd
      rw [eval_gradedPiece]
      exact if_neg (fun h => hd h.symm)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset (degreeSet_finite hP hν f)).mpr ⟨g, hg, rfl⟩) h

end Grading

section Characters

variable {D : Type uD} [CommGroup D]

/-- Evaluation of a character at a point, as a multiplicative map on the character group. -/
def characterEvaluation (d : D) : (D →* ℂˣ) →* ℂ where
  toFun χ := (χ d : ℂ)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem characterEvaluation_injective (hsep : ∀ d : D, d ≠ 1 → ∃ χ : D →* ℂˣ, χ d ≠ 1) :
    Function.Injective (characterEvaluation (D := D)) := by
  intro d e hde
  by_contra hne
  obtain ⟨χ, hχ⟩ := hsep (d * e⁻¹) (fun h => hne (mul_inv_eq_one.mp h))
  apply hχ
  have := congrArg (fun f : (D →* ℂˣ) →* ℂ => f χ) hde
  change (χ d : ℂ) = (χ e : ℂ) at this
  rw [map_mul, map_inv, Units.val_inj.mp this, mul_inv_cancel]

end Characters

section Extension

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {D : Type uD} [CommGroup D] [DecidableEq D]
  {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ P V}
  (ν : G →* D)
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
  (f0 : CompactFunctions P σ →ₗ[ℂ] W)

open Classical in
/-- Move a vector by an element of degree `d` and come back through `π`. The result does not
depend on the element chosen, when `f0` intertwines the kernel actions. -/
def degreeComponent (d : D) : CompactFunctions P σ →ₗ[ℂ] W :=
  if h : ∃ t, ν t = d then
    (π (Classical.choose h)⁻¹).comp (f0.comp (compactInduced P σ (Classical.choose h)))
  else 0

variable (hf0 : ∀ s ∈ ν.ker, ∀ v, f0 (compactInduced P σ s v) = π s (f0 v))
include hf0

theorem degreeComponent_eq (t : G) (w : CompactFunctions P σ) :
    degreeComponent ν π f0 (ν t) w = π t⁻¹ (f0 (compactInduced P σ t w)) := by
  have h : ∃ t', ν t' = ν t := ⟨t, rfl⟩
  rw [degreeComponent, dif_pos h]
  set t' := Classical.choose h with ht'
  have hν' : ν t' = ν t := Classical.choose_spec h
  have hk : t' * t⁻¹ ∈ ν.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hν', mul_inv_cancel]
  have ht'eq : t' = (t' * t⁻¹) * t := by group
  change π t'⁻¹ (f0 (compactInduced P σ t' w)) = _
  conv_lhs => rw [ht'eq, map_mul, Module.End.mul_apply, hf0 _ hk]
  rw [← Module.End.mul_apply (π _), ← map_mul]
  congr 2
  group

/-- Degree components of a translate. -/
theorem degreeComponent_translate (d : D) (m : G) (w : CompactFunctions P σ) :
    degreeComponent ν π f0 d (compactInduced P σ m w) =
      π m (degreeComponent ν π f0 (d * ν m) w) := by
  by_cases h : ∃ t, ν t = d
  · obtain ⟨t, rfl⟩ := h
    rw [degreeComponent_eq ν π f0 hf0, ← map_mul, degreeComponent_eq ν π f0 hf0]
    rw [← Module.End.mul_apply (compactInduced P σ t), ← map_mul]
    rw [← Module.End.mul_apply (π m), ← map_mul]
    congr 2
    group
  · have h' : ¬ ∃ t, ν t = d * ν m := by
      rintro ⟨t, ht⟩
      exact h ⟨t * m⁻¹, by rw [map_mul, ht, map_inv, mul_inv_cancel_right]⟩
    rw [degreeComponent, dif_neg h, degreeComponent, dif_neg h']
    simp

omit hf0 in
theorem degreeComponent_zero (d : D) : degreeComponent ν π f0 d 0 = 0 := map_zero _

variable (hP : P ≤ ν.ker) (hν : IsOpen (ν.ker : Set G))

/-- The underlying function of the twisted extension of `f0` by a character `χ` of `D`. -/
def twistedExtensionFun (χ : D →* ℂˣ) (z : CompactFunctions P σ) : W :=
  ∑ᶠ d, (χ d : ℂ) • degreeComponent ν π f0 d (gradedPiece hP hν d z)

omit hf0 in
theorem twistedExtensionFun_eq_sum (χ : D →* ℂˣ) (z : CompactFunctions P σ) {S : Finset D}
    (hS : degreeSet ν z ⊆ S) :
    twistedExtensionFun ν π f0 hP hν χ z =
      ∑ d ∈ S, (χ d : ℂ) • degreeComponent ν π f0 d (gradedPiece hP hν d z) := by
  apply finsum_eq_sum_of_support_subset
  intro d hd
  by_contra hdS
  apply hd
  change (χ d : ℂ) • degreeComponent ν π f0 d (gradedPiece hP hν d z) = 0
  rw [gradedPiece_eq_zero_of_notMem hP hν z (fun h => hdS (hS h)), map_zero, smul_zero]

omit hf0 in
theorem degreeSet_add_subset (z w : CompactFunctions P σ) :
    degreeSet ν (z + w) ⊆ degreeSet ν z ∪ degreeSet ν w := by
  rintro _ ⟨g, hg, rfl⟩
  by_contra h
  simp only [Set.mem_union, not_or] at h
  apply hg
  rw [eval_add]
  have h1 : eval P σ z.1 g = 0 := by
    by_contra h'
    exact h.1 ⟨g, h', rfl⟩
  have h2 : eval P σ w.1 g = 0 := by
    by_contra h'
    exact h.2 ⟨g, h', rfl⟩
  rw [h1, h2, add_zero]

omit hf0 in
theorem degreeSet_smul_subset (a : ℂ) (z : CompactFunctions P σ) :
    degreeSet ν (a • z) ⊆ degreeSet ν z := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  intro h
  apply hg
  rw [eval_smul, h, smul_zero]

omit hf0 in
theorem degreeSet_translate_subset (m : G) (z : CompactFunctions P σ) :
    degreeSet ν (compactInduced P σ m z) ⊆ (fun d => d * (ν m)⁻¹) '' degreeSet ν z := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨ν (g * m), ⟨g * m, hg, rfl⟩, ?_⟩
  simp

/-- The twisted extension: an intertwiner from compact induction to `(χ ∘ ν)⁻¹ ⊗ π`. -/
def twistedExtension (χ : D →* ℂˣ) :
    (compactInduced P σ).IntertwiningMap (twist (χ.comp ν)⁻¹ π) where
  toFun := twistedExtensionFun ν π f0 hP hν χ
  map_add' z w := by
    classical
    let S := (degreeSet_finite hP hν z).toFinset ∪ (degreeSet_finite hP hν w).toFinset
    have hz : degreeSet ν z ⊆ S := fun d hd => Finset.mem_union_left _
      ((Set.Finite.mem_toFinset _).mpr hd)
    have hw : degreeSet ν w ⊆ S := fun d hd => Finset.mem_union_right _
      ((Set.Finite.mem_toFinset _).mpr hd)
    have hzw : degreeSet ν (z + w) ⊆ S := fun d hd => by
      rcases degreeSet_add_subset ν z w hd with h | h
      · exact hz h
      · exact hw h
    rw [twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hzw,
      twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hz,
      twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hw, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← gradedProjection_apply, map_add, map_add, smul_add, gradedProjection_apply,
      gradedProjection_apply]
  map_smul' a z := by
    classical
    let S := (degreeSet_finite hP hν z).toFinset
    have hz : degreeSet ν z ⊆ S := fun d hd => (Set.Finite.mem_toFinset _).mpr hd
    rw [twistedExtensionFun_eq_sum ν π f0 hP hν χ _ ((degreeSet_smul_subset ν a z).trans hz),
      twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hz, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [← gradedProjection_apply, map_smul, map_smul, gradedProjection_apply, smul_comm]
  isIntertwining' m := by
    classical
    ext z
    let S := (degreeSet_finite hP hν z).toFinset
    have hz : degreeSet ν z ⊆ S := fun d hd => (Set.Finite.mem_toFinset _).mpr hd
    have hmz : degreeSet ν (compactInduced P σ m z) ⊆ S.image (fun d => d * (ν m)⁻¹) := by
      intro d hd
      obtain ⟨e, he, rfl⟩ := degreeSet_translate_subset ν m z hd
      exact Finset.mem_image_of_mem _ (hz he)
    change twistedExtensionFun ν π f0 hP hν χ (compactInduced P σ m z) =
      ((((χ.comp ν)⁻¹ m : ℂˣ) : ℂ)) • π m (twistedExtensionFun ν π f0 hP hν χ z)
    rw [twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hmz,
      twistedExtensionFun_eq_sum ν π f0 hP hν χ _ hz,
      Finset.sum_image (fun a _ b _ h => mul_right_cancel h), map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [gradedPiece_translate, inv_mul_cancel_right,
      degreeComponent_translate ν π f0 hf0, inv_mul_cancel_right, map_smul, smul_smul]
    congr 1
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, map_mul, map_inv, Units.val_mul]
    ring

theorem twistedExtension_apply (χ : D →* ℂˣ) (z : CompactFunctions P σ) :
    twistedExtension ν π f0 hf0 hP hν χ z = twistedExtensionFun ν π f0 hP hν χ z := rfl

/-- If `f0` detects a translated graded piece, some twisted extension is nonzero. -/
theorem exists_twistedExtension_ne_zero
    (hsep : ∀ d : D, d ≠ 1 → ∃ χ : D →* ℂˣ, χ d ≠ 1)
    (z : CompactFunctions P σ) (t : G)
    (hz : f0 (compactInduced P σ t (gradedPiece hP hν (ν t) z)) ≠ 0) :
    ∃ χ : D →* ℂˣ, twistedExtension ν π f0 hf0 hP hν χ z ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  let S := (degreeSet_finite hP hν z).toFinset
  have hzS : degreeSet ν z ⊆ S := fun d hd => (Set.Finite.mem_toFinset _).mpr hd
  let c : D → W := fun d => degreeComponent ν π f0 d (gradedPiece hP hν d z)
  have hli := (linearIndependent_monoidHom (D →* ℂˣ) ℂ).comp _
    (characterEvaluation_injective (D := D) hsep)
  have hc : ∀ d ∈ S, c d = 0 := by
    intro d hd
    apply (Module.forall_dual_apply_eq_zero_iff ℂ (c d)).mp
    intro φ
    have hsum := (linearIndependent_iff'.mp hli) S (fun e => φ (c e)) (by
      funext χ
      have h0 := hall χ
      rw [twistedExtension_apply, twistedExtensionFun_eq_sum ν π f0 hP hν χ z hzS] at h0
      have h1 := congrArg φ h0
      rw [map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul] at h1
      simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← h1]
      apply Finset.sum_congr rfl
      intro e _
      change φ (c e) * (χ e : ℂ) = (χ e : ℂ) * φ (c e)
      ring) d hd
    exact hsum
  have hmem : ν t ∈ S := by
    apply hzS
    by_contra hnot
    apply hz
    rw [gradedPiece_eq_zero_of_notMem hP hν z hnot, map_zero, map_zero]
  have hct := hc (ν t) hmem
  change degreeComponent ν π f0 (ν t) (gradedPiece hP hν (ν t) z) = 0 at hct
  rw [degreeComponent_eq ν π f0 hf0] at hct
  apply hz
  have := congrArg (π t) hct
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
    map_zero] at this

end Extension

end Langlands.RankinSelberg.SupercuspidalCompleteness
