import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution
import Langlands.Group.GL.Blocks

/-!
# Cusp forms on `GL_n`: vanishing constant terms and split tensor products

Harish-Chandra's cusp forms on `GL_n(R)` for a commutative topological ring `R`: functions all
of whose constant terms along proper standard block parabolic subgroups vanish, after every
two-sided translation and for every Haar measure on the unipotent radical
(`HasVanishingConstantTerms`). The vanishing integral is the Library's
`Langlands.HarishChandraSchwartz.IsUnipotentCuspidal`. Also the tensor product
`φ_0 ⊗ … ⊗ φ_{l-1}` of functions on `GL_n(F)`, as a function on `GL_n(F^l)` (`splitTensor`).

Sources: Henniart-Lemaire 2011, II.6.3 (the condition `c_{v₁}(f)`); Casselman 1995, §5;
Arthur-Clozel 1989, Chapter 1, §5. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

universe u

section VanishingConstantTerms

/-- **Cusp forms** (vanishing constant terms). For every proper standard block parabolic
subgroup `P = M U` of `GL_n(R)` (a block shape with at least two blocks) and every Haar
measure `μ` on its unipotent radical `U` (Borel σ-algebra of `GL_n(R)`, subspace σ-algebra on
`U`), each function `u ↦ f (x * u * y)` is `μ`-integrable and the Library's
`IsUnipotentCuspidal μ f` holds: `∫_U f (x * u * y) dμ(u) = 0` for all `x y`. -/
def HasVanishingConstantTerms {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {n : ℕ} (f : GeneralLinear n R → ℂ) : Prop :=
  letI : MeasurableSpace (GeneralLinear n R) := borel _
  ∀ B : GeneralLinear.BlockShape n, 2 ≤ B.length →
    ∀ μ : Measure (B.unipotentSubgroup R), μ.IsHaarMeasure →
      (∀ x y : GeneralLinear n R, Integrable
        (fun u : B.unipotentSubgroup R => f (x * (u : GeneralLinear n R) * y)) μ) ∧
      HarishChandraSchwartz.IsUnipotentCuspidal μ f

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}

/-- The zero function is a cusp form. -/
theorem hasVanishingConstantTerms_zero :
    HasVanishingConstantTerms (fun _ : GeneralLinear n R => (0 : ℂ)) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B _ μ _
  refine ⟨fun x y => integrable_zero _ _ μ, fun x y => ?_⟩
  exact integral_zero _ _

namespace HasVanishingConstantTerms

variable {f g : GeneralLinear n R → ℂ}

/-- Cusp forms are closed under addition. -/
theorem add (hf : HasVanishingConstantTerms f) (hg : HasVanishingConstantTerms g) :
    HasVanishingConstantTerms (fun x => f x + g x) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B hB μ hμ
  obtain ⟨hfi, hfc⟩ := hf B hB μ hμ
  obtain ⟨hgi, hgc⟩ := hg B hB μ hμ
  refine ⟨fun x y => (hfi x y).add (hgi x y), fun x y => ?_⟩
  change ∫ u : B.unipotentSubgroup R,
      (f (x * (u : GeneralLinear n R) * y) + g (x * (u : GeneralLinear n R) * y)) ∂μ = 0
  rw [integral_add (hfi x y) (hgi x y), hfc x y, hgc x y, add_zero]

/-- Cusp forms are closed under negation. -/
theorem neg (hf : HasVanishingConstantTerms f) :
    HasVanishingConstantTerms (fun x => -f x) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B hB μ hμ
  obtain ⟨hfi, hfc⟩ := hf B hB μ hμ
  refine ⟨fun x y => (hfi x y).neg, fun x y => ?_⟩
  change ∫ u : B.unipotentSubgroup R, -f (x * (u : GeneralLinear n R) * y) ∂μ = 0
  rw [integral_neg, hfc x y, neg_zero]

/-- Cusp forms are closed under subtraction. -/
theorem sub (hf : HasVanishingConstantTerms f) (hg : HasVanishingConstantTerms g) :
    HasVanishingConstantTerms (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Cusp forms are closed under multiplication by a complex scalar. -/
theorem const_mul (hf : HasVanishingConstantTerms f) (c : ℂ) :
    HasVanishingConstantTerms (fun x => c * f x) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B hB μ hμ
  obtain ⟨hfi, hfc⟩ := hf B hB μ hμ
  refine ⟨fun x y => (hfi x y).const_mul c, fun x y => ?_⟩
  change ∫ u : B.unipotentSubgroup R, c * f (x * (u : GeneralLinear n R) * y) ∂μ = 0
  rw [integral_const_mul, hfc x y, mul_zero]

/-- Cusp forms are closed under left translation: `g ↦ f (a * g)`. -/
theorem comp_mul_left (hf : HasVanishingConstantTerms f) (a : GeneralLinear n R) :
    HasVanishingConstantTerms (fun g => f (a * g)) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B hB μ hμ
  obtain ⟨hfi, hfc⟩ := hf B hB μ hμ
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · simpa only [mul_assoc] using hfi (a * x) y
  · change ∫ u : B.unipotentSubgroup R, f (a * (x * (u : GeneralLinear n R) * y)) ∂μ = 0
    simpa only [mul_assoc] using hfc (a * x) y

/-- Cusp forms are closed under right translation: `g ↦ f (g * a)`. -/
theorem comp_mul_right (hf : HasVanishingConstantTerms f) (a : GeneralLinear n R) :
    HasVanishingConstantTerms (fun g => f (g * a)) := by
  let _ : MeasurableSpace (GeneralLinear n R) := borel _
  intro B hB μ hμ
  obtain ⟨hfi, hfc⟩ := hf B hB μ hμ
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · simpa only [mul_assoc] using hfi x (y * a)
  · change ∫ u : B.unipotentSubgroup R, f (x * (u : GeneralLinear n R) * y * a) ∂μ = 0
    simpa only [mul_assoc] using hfc x (y * a)

end HasVanishingConstantTerms

/-- A finite sum of cusp forms is a cusp form. -/
theorem hasVanishingConstantTerms_sum {ι : Type*} (s : Finset ι)
    (f : ι → GeneralLinear n R → ℂ) (hf : ∀ i ∈ s, HasVanishingConstantTerms (f i)) :
    HasVanishingConstantTerms (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using hasVanishingConstantTerms_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- For `n ≤ 1` there is no proper block parabolic, so every function is a cusp form. -/
theorem hasVanishingConstantTerms_of_le_one (hn : n ≤ 1) (f : GeneralLinear n R → ℂ) :
    HasVanishingConstantTerms f := by
  intro B hB
  have := B.length_le
  omega

end VanishingConstantTerms

section SplitTensor

variable {F : Type u} [CommRing F] {l n : ℕ}

/-- The **split tensor product** `φ_0 ⊗ … ⊗ φ_{l-1}` on `GL_n(F^l) = GL_n(F)^l`:
`g ↦ ∏ i, φ i (g_i)`, where `g_i` is the image of `g` under the `i`-th coordinate projection
`F^l → F`. -/
def splitTensor (φ : Fin l → GeneralLinear n F → ℂ) : GeneralLinear n (Fin l → F) → ℂ :=
  fun g => ∏ i, φ i (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g)

theorem splitTensor_apply (φ : Fin l → GeneralLinear n F → ℂ)
    (g : GeneralLinear n (Fin l → F)) :
    splitTensor φ g =
      ∏ i, φ i (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g) :=
  rfl

end SplitTensor

end Langlands.BaseChange
