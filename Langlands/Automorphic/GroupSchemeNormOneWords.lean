import Langlands.Automorphic.GroupSchemeNormOneDirectional
import Langlands.Global.AdelicNormOneFamilyDecay

/-! # Word derivatives on the norm-one adelic group

`normOneWordDerivative A w f` applies the coordinate derivatives of the letters of `w` to `f`, the
last letter first. It is the operator `normOneDifferential A` of the single word `w`. For an
input of class `Cⁿ` at a fixed level, the word derivatives of length at most `n` are of class
`C^{n - |w|}`. A word derivative with differentiable slices and continuous coordinate derivatives
satisfies `IsNormOnePathDerivative` after extension along a norm-one retraction. For a fixed-level
`Cⁿ` input these regularity conditions hold when `w.length < n`. -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

local notation "G¹" => normOneSubgroup F G
local notation "G∞¹" => infiniteNormOneSubgroup F G
local notation "ι" => infiniteNormOneInclusion F G
local notation "IE" => 𝓘(ℝ, Fin e → ℝ)

/-- The coordinate derivatives of the letters of `w` applied to `f`, the last letter first. -/
def normOneWordDerivative (A : NormOneLieAtlas F G hsmooth e) :
    List (Fin e) → (G¹ → ℂ) → G¹ → ℂ
  | [], f => f
  | l :: w, f => normOneDirectional A (Pi.single l 1) (normOneWordDerivative A w f)

@[simp] theorem normOneWordDerivative_nil (A : NormOneLieAtlas F G hsmooth e) (f : G¹ → ℂ) :
    normOneWordDerivative A [] f = f := rfl

@[simp] theorem normOneWordDerivative_cons (A : NormOneLieAtlas F G hsmooth e) (l : Fin e)
    (w : List (Fin e)) (f : G¹ → ℂ) :
    normOneWordDerivative A (l :: w) f =
      normOneDirectional A (Pi.single l 1) (normOneWordDerivative A w f) := rfl

/-- The single word `w` as a differential operator. -/
def normOneWord (w : List (Fin e)) : NormOneDifferentialWord e :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

theorem normOneWord_orderLE (w : List (Fin e)) : (normOneWord w).OrderLE w.length := by
  intro v hv
  have hv' : v = FreeMonoid.ofList w := by
    simpa [normOneWord, MonoidAlgebra.coeff_single, Finsupp.mem_support_iff,
      Finsupp.single_apply] using hv
  rw [hv']
  rfl

/-- The finite set of words of length at most `r` in the letters `Fin e`. -/
def normOneWordsUpTo (e r : ℕ) : Finset (List (Fin e)) :=
  (Finset.range (r + 1)).biUnion fun k =>
    Finset.univ.image (List.ofFn : (Fin k → Fin e) → List (Fin e))

theorem mem_normOneWordsUpTo {e r : ℕ} {w : List (Fin e)} :
    w ∈ normOneWordsUpTo e r ↔ w.length ≤ r := by
  simp only [normOneWordsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, f, rfl⟩
    simpa only [List.length_ofFn] using Nat.lt_succ_iff.mp hk
  · intro h
    exact ⟨w.length, Nat.lt_succ_of_le h, w.get, List.ofFn_get w⟩

/-- The slice of a word derivative is the word derivative of the slice. -/
theorem normOneInfiniteSlice_normOneWordDerivative (A : NormOneLieAtlas F G hsmooth e)
    (w : List (Fin e)) (f : G¹ → ℂ) (x : G¹) :
    letI := A.chartedSpace
    letI := A.lieGroup
    normOneInfiniteSlice F G (normOneWordDerivative A w f) x =
      (lieWordDerivative (fun j : Fin e => (Pi.single j (1 : ℝ) : Fin e → ℝ)) (FreeMonoid.ofList w) :
        (G∞¹ → ℂ) → G∞¹ → ℂ) (normOneInfiniteSlice F G f x) := by
  let := A.chartedSpace
  let := A.lieGroup
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [normOneWordDerivative_cons, normOneInfiniteSlice_normOneDirectional, ih,
      FreeMonoid.ofList_cons, map_mul]
    rfl

/-- **Words as differential operators.** -/
theorem normOneDifferential_normOneWord (A : NormOneLieAtlas F G hsmooth e)
    (w : List (Fin e)) (f : G¹ → ℂ) (x : G¹) :
    normOneDifferential A (normOneWord w) f x = normOneWordDerivative A w f x := by
  let := A.chartedSpace
  let := A.lieGroup
  have h := congrFun (normOneInfiniteSlice_normOneWordDerivative A w f x) 1
  simp only [normOneInfiniteSlice, map_one, mul_one] at h
  rw [h]
  simp only [normOneDifferential, lieWordAction, normOneWord, MonoidAlgebra.coeff_single]
  rw [Finsupp.sum_single_index (by simp), one_smul]

/-- **Finite-order regularity of word derivatives.** -/
theorem isNormOneCr_normOneWordDerivative (A : NormOneLieAtlas F G hsmooth e)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))} {f : G¹ → ℂ} {n : ℕ}
    (hf : IsNormOneCr A n K₀ hK₀ f) (w : List (Fin e)) (hw : w.length ≤ n) :
    IsNormOneCr A ((n - w.length : ℕ) : WithTop ℕ∞) K₀ hK₀ (normOneWordDerivative A w f) := by
  induction w with
  | nil => simpa using hf
  | cons l w ih =>
    have hw' : w.length ≤ n := (Nat.le_succ _).trans (by simpa using hw)
    refine isNormOneCr_normOneDirectional A (m := ((n - (l :: w).length : ℕ) : WithTop ℕ∞))
      (n := ((n - w.length : ℕ) : WithTop ℕ∞)) ?_ ?_ _ (ih hw')
    · have h1 : n - (l :: w).length + 1 = n - w.length := by
        simp only [List.length_cons] at hw ⊢
        omega
      rw [← h1]
      push_cast
      exact le_rfl
    · exact WithTop.coe_le_coe.mpr le_top

/-- The inclusion of `G(F∞)¹` in `G(𝔸)¹` is continuous. -/
theorem continuous_infiniteNormOneInclusion : Continuous (ι : G∞¹ → G¹) :=
  Continuous.subtype_mk ((ofInfinite F G).continuous.comp continuous_subtype_val) _

/-- **Integrated derivative identity for an extension along a norm-one retraction.** If the
slices of `ψ` are differentiable and its coordinate derivatives are continuous, then `ψ ∘ r`
(for a map `r` fixing norm-one points) has the coordinate derivatives `D_l ψ ∘ r` along smooth
paths at norm-one points. -/
theorem isNormOnePathDerivative_comp_retraction (A : NormOneLieAtlas F G hsmooth e)
    [LocallyOfFiniteType G.X.hom]
    (r : AdelicGroupPoints F G → G¹) (hr : ∀ n : G¹, r n = n) {ψ : G¹ → ℂ}
    (hd : letI := A.chartedSpace
      ∀ x, MDifferentiable IE 𝓘(ℝ, ℂ) (normOneInfiniteSlice F G ψ x))
    (hc : ∀ l, Continuous (normOneDirectional A (Pi.single l 1) ψ)) :
    IsNormOnePathDerivative A (fun x => ψ (r x))
      (fun l x => normOneDirectional A (Pi.single l 1) ψ (r x)) := by
  let := A.chartedSpace
  let := A.lieGroup
  intro y hy c V hcs hV hVc
  let y₁ : G¹ := ⟨y, hy⟩
  have hpt (t : ℝ) : r (y * ofInfinite F G (c t)) = y₁ * ι (c t) := hr (y₁ * ι (c t))
  simp only [hpt]
  have hcc : Continuous c := hcs.continuous
  have hpath : Continuous fun t : ℝ => y₁ * ι (c t) :=
    continuous_const.mul (continuous_infiniteNormOneInclusion.comp hcc)
  have hderiv (t : ℝ) : HasDerivAt (fun s => ψ (y₁ * ι (c s)))
      (∑ l : Fin e, (V t l : ℂ) * normOneDirectional A (Pi.single l 1) ψ (y₁ * ι (c t))) t := by
    have h := hasDerivAt_normOne_path A (hV t) ((hd y₁) (c t)) (hcs.mdifferentiableAt (by simp))
    rwa [normOneDirectional_eq_sum] at h
  have hcont : Continuous fun t : ℝ =>
      ∑ l : Fin e, (V t l : ℂ) * normOneDirectional A (Pi.single l 1) ψ (y₁ * ι (c t)) :=
    continuous_finsetSum _ fun l _ =>
      (Complex.continuous_ofReal.comp ((continuous_apply l).comp hVc)).mul ((hc l).comp hpath)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 1)).symm

/-- Slices of a word derivative of a `Cⁿ` input are differentiable while `|w| < n`. -/
theorem mdifferentiable_slice_normOneWordDerivative (A : NormOneLieAtlas F G hsmooth e)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))} {f : G¹ → ℂ} {n : ℕ}
    (hf : IsNormOneCr A n K₀ hK₀ f) (w : List (Fin e)) (hw : w.length < n) (x : G¹) :
    letI := A.chartedSpace
    MDifferentiable IE 𝓘(ℝ, ℂ) (normOneInfiniteSlice F G (normOneWordDerivative A w f) x) := by
  let := A.chartedSpace
  have h := (isNormOneCr_normOneWordDerivative A hf w hw.le).2.2 x
  refine h.mdifferentiable ?_
  have hpos : 0 < n - w.length := Nat.sub_pos_of_lt hw
  exact_mod_cast hpos.ne'

/-- **Joint measurability of word derivatives of a family.** -/
theorem measurable_normOneWordDerivative (A : NormOneLieAtlas F G hsmooth e)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))} {Ω : Type*} [MeasurableSpace Ω]
    {φ : Ω → G¹ → ℂ} {n : ℕ} (hφ : ∀ o, IsNormOneCr A n K₀ hK₀ (φ o))
    (hm : Measurable (fun p : Ω × G¹ => φ p.1 p.2)) (w : List (Fin e)) (hw : w.length ≤ n) :
    Measurable (fun p : Ω × G¹ => normOneWordDerivative A w (φ p.1) p.2) := by
  induction w with
  | nil => simpa using hm
  | cons l w ih =>
    have hw' : w.length < n := by simpa using hw
    simp only [normOneWordDerivative_cons]
    exact measurable_normOneDirectional A (Pi.single l 1)
      (ψ := fun o => normOneWordDerivative A w (φ o)) (ih hw'.le)
      (fun o y => (mdifferentiable_slice_normOneWordDerivative A (hφ o) w hw' y) 1)

end Langlands.Automorphic.GroupSchemeFunctions
