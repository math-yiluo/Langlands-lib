import Langlands.BaseChange.Norm
import Langlands.BaseChange.CuspForm
import Langlands.Representation.Hecke.Convolution
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Algebra.Pi

/-!
# Cyclic base change for `GL_n` at a split place

At a place where the cyclic extension splits completely, the local algebra is `F^l`
(`Fin l → F`) with the cyclic shift `(σ x) i = x (i + 1)` (Arthur–Clozel 1989, Chapter 1,
§5, printed p. 48; Henniart–Lemaire 2011, II.2.15, printed p. 76). This module defines:

* the cyclic shift `splitCyclicShift F l` of `F^l`;
* the convolution product `φ 0 * (φ 1 * (⋯ * φ l))` of test functions
  (`convolutionProduct`), for the Library's `Hecke.TestFunction.convolution`;
* `IsSplitProductHaar μF μE`: `μE` integrates split tensors `ψ₀ ⊗ ⋯ ⊗ ψ_{l-1}` as the product
  measure `μF ⊗ ⋯ ⊗ μF` would;
* the tensor power representation `splitTensorRep ρ : g ↦ ρ(g₀) ⊗ ⋯ ⊗ ρ(g_{l-1})` of
  `GL_n(F^l)` on `⨂[ℂ] _ : Fin l, V`, and the cyclic shift `splitTensorShift V l` of the tensor
  factors.

`GL_n(F^l)` is never identified with `GL_n(F)^l`: the `i`-th component of `g : GL_n(F^l)` is
its image under the coordinate map `Pi.evalRingHom _ i`. The lemmas record the defining
formulas, that `splitTensorShift` intertwines `splitTensorRep ρ` with its twist by the shift,
and that `F^{l+1}` with the shift is a cyclic algebra. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

universe u v w

/-! ## The cyclic shift of `F^l` -/

section Shift

open Fin.NatCast

/-- The cyclic shift `(σ x) i = x (i + 1)` of `F^l = Fin l → F`, indices modulo `l`
(Arthur–Clozel 1989, Chapter 1, §5: `σ(x₁, …, x_m) = (x₂, …, x_m, x₁)`). -/
def splitCyclicShift (F : Type u) [CommSemiring F] (l : ℕ) :
    (Fin l → F) ≃ₐ[F] (Fin l → F) :=
  AlgEquiv.piCongrLeft' F (fun _ : Fin l => F) (finRotate l).symm

/-- `splitCyclicShift F l x i = x (finRotate l i)`, where `finRotate l i = i + 1`. -/
@[simp]
theorem splitCyclicShift_apply (F : Type u) [CommSemiring F] (l : ℕ) (x : Fin l → F)
    (i : Fin l) : splitCyclicShift F l x i = x (finRotate l i) :=
  rfl

/-- The powers of the shift: `(σ ^ k) x i = x ((finRotate l ^ k) i)`. -/
theorem splitCyclicShift_pow_apply (F : Type u) [CommSemiring F] (l k : ℕ) (x : Fin l → F)
    (i : Fin l) : (splitCyclicShift F l ^ k) x i = x ((finRotate l ^ k) i) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, splitCyclicShift_apply, pow_succ',
      Equiv.Perm.mul_apply]

/-- `(finRotate (l + 1) ^ k) i = i + k`. -/
theorem finRotate_succ_pow_apply (l k : ℕ) (i : Fin (l + 1)) :
    (finRotate (l + 1) ^ k) i = i + ((k : ℕ) : Fin (l + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply, Nat.cast_succ, add_assoc]

/-- For a field `F`, `F^{l+1}` with the cyclic shift is a cyclic `F`-algebra of degree
`l + 1` (Henniart–Lemaire 2011, I.2.1 and II.2.15). -/
theorem isCyclicAlgebra_splitCyclicShift (F : Type u) [Field F] (l : ℕ) :
    IsCyclicAlgebra (splitCyclicShift F (l + 1)) (l + 1) := by
  refine ⟨inferInstance, Module.finrank_fin_fun F, inferInstance, ?_, ?_⟩
  · rw [orderOf_eq_iff (Nat.succ_pos l)]
    refine ⟨?_, ?_⟩
    · refine AlgEquiv.ext fun x => funext fun i => ?_
      rw [splitCyclicShift_pow_apply, finRotate_succ_pow_apply, Fin.natCast_self, add_zero]
      rfl
    · intro m hm hm0 h
      have hx := congr_fun (congr_arg (fun τ : (Fin (l + 1) → F) ≃ₐ[F] (Fin (l + 1) → F) =>
        τ (Pi.single 0 1)) h) 0
      simp only [splitCyclicShift_pow_apply, finRotate_succ_pow_apply, zero_add,
        AlgEquiv.one_apply] at hx
      have hm' : ((m : ℕ) : Fin (l + 1)) ≠ 0 := by
        intro h0
        rw [Fin.natCast_eq_zero] at h0
        exact absurd (Nat.le_of_dvd hm0 h0) (not_le.mpr hm)
      rw [Pi.single_eq_of_ne hm', Pi.single_eq_same] at hx
      exact zero_ne_one hx
  · intro x hx
    refine ⟨x 0, funext fun i => ?_⟩
    rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [ih]
      have := congr_fun hx (Fin.castSucc i)
      rw [splitCyclicShift_apply, finRotate_apply, Fin.coeSucc_eq_succ] at this
      exact this.symm

end Shift

/-! ## Convolution products of test functions -/

section Convolution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The convolution product `φ 0 * (φ 1 * (⋯ * φ l))` of `l + 1` test functions, for the
Library's convolution `(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`. -/
def convolutionProduct (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    {l : ℕ} → (Fin (l + 1) → SchwartzBruhat G) → SchwartzBruhat G
  | 0, φ => φ 0
  | _ + 1, φ => Hecke.TestFunction.convolution μ (φ 0) (convolutionProduct μ (Fin.tail φ))

omit [BorelSpace G] in
theorem convolutionProduct_zero (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (φ : Fin 1 → SchwartzBruhat G) : convolutionProduct μ φ = φ 0 :=
  rfl

omit [BorelSpace G] in
theorem convolutionProduct_succ (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {l : ℕ}
    (φ : Fin (l + 2) → SchwartzBruhat G) :
    convolutionProduct μ φ =
      Hecke.TestFunction.convolution μ (φ 0) (convolutionProduct μ (Fin.tail φ)) :=
  rfl

end Convolution

/-! ## Product Haar measures at a split place -/

/-- `μE` on `GL_n(F^l)` integrates every split tensor `ψ₀ ⊗ ⋯ ⊗ ψ_{l-1}` of test functions on
`GL_n(F)` to the product of the `μF`-integrals of its factors. Under
`GL_n(F^l) = GL_n(F)^l` this says that `μE` is the product measure `μF ⊗ ⋯ ⊗ μF`
(Henniart–Lemaire 2011, II.2.15: `dg_E = (dg)^d`). -/
def IsSplitProductHaar {F : Type u} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
    {n l : ℕ} [MeasurableSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n (Fin l → F))]
    (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n (Fin l → F))) : Prop :=
  ∀ ψ : Fin l → SchwartzBruhat (GeneralLinear n F),
    ∫ g, splitTensor (fun i => (ψ i : GeneralLinear n F → ℂ)) g ∂μE = ∏ i, ∫ g, ψ i g ∂μF

/-! ## Tensor powers of representations -/

section Tensor

variable {F : Type u} [CommRing F] {n l : ℕ} {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The representation `g ↦ ρ(g₀) ⊗ ⋯ ⊗ ρ(g_{l-1})` of `GL_n(F^l)` on `⨂[ℂ] _ : Fin l, V`,
with `g_i` the image of `g` under the `i`-th coordinate map: the representation
`ρ ⊗ ⋯ ⊗ ρ` of `GL_n(F)^l`. -/
def splitTensorRep (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (GeneralLinear n (Fin l → F)) (PiTensorProduct ℂ fun _ : Fin l => V) :=
  (PiTensorProduct.mapMonoidHom (R := ℂ) (s := fun _ : Fin l => V)).comp
    (MonoidHom.pi fun i =>
      ρ.comp (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i)))

theorem splitTensorRep_tprod (ρ : Representation ℂ (GeneralLinear n F) V)
    (g : GeneralLinear n (Fin l → F)) (v : Fin l → V) :
    splitTensorRep ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun i =>
        ρ (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g) (v i) := by
  simp [splitTensorRep]

variable (V) in
/-- The cyclic shift of the tensor factors, `v₀ ⊗ v₁ ⊗ ⋯ ⊗ v_{l-1} ↦ v₁ ⊗ ⋯ ⊗ v_{l-1} ⊗ v₀`. -/
def splitTensorShift (l : ℕ) :
    (PiTensorProduct ℂ fun _ : Fin l => V) ≃ₗ[ℂ] (PiTensorProduct ℂ fun _ : Fin l => V) :=
  PiTensorProduct.reindex ℂ (fun _ : Fin l => V) (finRotate l).symm

variable (V) in
theorem splitTensorShift_tprod (l : ℕ) (v : Fin l → V) :
    splitTensorShift V l (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun i => v (finRotate l i) := by
  simp [splitTensorShift]

/-- The `i`-th component of `g^σ` is the `(i + 1)`-th component of `g`. -/
theorem map_evalRingHom_entrywiseAut_splitCyclicShift (g : GeneralLinear n (Fin l → F))
    (i : Fin l) :
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i)
        (entrywiseAut (splitCyclicShift F l) n g) =
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) (finRotate l i)) g := by
  ext a b
  rfl

/-- `splitTensorShift` intertwines `splitTensorRep ρ` with its twist
`g ↦ splitTensorRep ρ (g^σ)` by the cyclic shift `σ`. -/
theorem splitTensorShift_comp (ρ : Representation ℂ (GeneralLinear n F) V)
    (g : GeneralLinear n (Fin l → F)) :
    (splitTensorShift V l).toLinearMap ∘ₗ splitTensorRep ρ g =
      splitTensorRep ρ (entrywiseAut (splitCyclicShift F l) n g) ∘ₗ
        (splitTensorShift V l).toLinearMap := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, splitTensorRep_tprod, splitTensorShift_tprod,
    map_evalRingHom_entrywiseAut_splitCyclicShift]

end Tensor

end Langlands.BaseChange
