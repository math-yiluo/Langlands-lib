import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-! # Rearranging finite products of measures

Generic lemmas for the proof of `RectangleTateStatement`: scalar multiples in finite product
measures, and the measure-preserving rearrangements between iterated finite products
`(a → b → β)`, `(a × b → β)` and `(b → a → β)`, and between matrices of pairs and pairs of
matrices.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RectangleTate

section Generic

variable {a b : Type*} [Fintype a] [Fintype b] {β γ : Type*} [MeasurableSpace β]
  [MeasurableSpace γ]

/-- A finite product of finite scalar multiples of measures is the product of the scalars times
the product measure. -/
theorem pi_smul_eq (μ : a → Measure β) [∀ i, SigmaFinite (μ i)] (c : a → NNReal) :
    Measure.pi (fun i => c i • μ i) = (∏ i, (c i : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ENNReal.smul_def,
    Finset.prod_mul_distrib]

/-- Uncurrying iterated finite products of measures. -/
theorem measurePreserving_uncurry (μ : a → b → Measure β) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry a b β).symm
      (Measure.pi fun i => Measure.pi fun j => μ i j)
      (Measure.pi fun p : a × b => μ p.1 p.2) := by
  refine ⟨(MeasurableEquiv.curry a b β).symm.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.curry a b β).symm ⁻¹' Set.pi univ s =
      Set.pi univ fun i => Set.pi univ fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Finset.univ_product_univ, Finset.prod_product]

/-- Swapping the two indices of an iterated finite product of measures. -/
theorem measurePreserving_swap (μ : a → b → Measure β) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (fun (f : a → b → β) (j : b) (i : a) => f i j)
      (Measure.pi fun i : a => Measure.pi fun j : b => μ i j)
      (Measure.pi fun j : b => Measure.pi fun i : a => μ i j) := by
  have h1 := measurePreserving_uncurry μ
  have h2 := measurePreserving_piCongrLeft (fun p : b × a => μ p.2 p.1) (Equiv.prodComm a b)
  have h3 := (measurePreserving_uncurry (fun j i => μ i j)).symm
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext f
  funext j i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, MeasurableEquiv.curry,
    Function.uncurry]

/-- Splitting a matrix of pairs into a pair of matrices. -/
theorem measurePreserving_matrixProd (μ : Measure β) (ν : Measure γ) [SigmaFinite μ]
    [SigmaFinite ν] :
    MeasurePreserving
      (fun (M : a → b → β × γ) => ((fun i j => (M i j).1), (fun i j => (M i j).2)))
      (Measure.pi fun _ : a => Measure.pi fun _ : b => μ.prod ν)
      ((Measure.pi fun _ : a => Measure.pi fun _ : b => μ).prod
        (Measure.pi fun _ : a => Measure.pi fun _ : b => ν)) := by
  have h1 : MeasurePreserving (fun (M : a → b → β × γ) i =>
      MeasurableEquiv.arrowProdEquivProdArrow β γ b (M i))
      (Measure.pi fun _ : a => Measure.pi fun _ : b => μ.prod ν)
      (Measure.pi fun _ : a => (Measure.pi fun _ : b => μ).prod (Measure.pi fun _ : b => ν)) :=
    measurePreserving_pi _ _ fun _ =>
      measurePreserving_arrowProdEquivProdArrow β γ b (fun _ => μ) (fun _ => ν)
  have h2 := measurePreserving_arrowProdEquivProdArrow (b → β) (b → γ) a
    (fun _ => Measure.pi fun _ : b => μ) (fun _ => Measure.pi fun _ : b => ν)
  convert h2.comp h1 using 1
  funext M
  rfl

/-- Merging a pair of matrices into a matrix of pairs. -/
theorem measurePreserving_matrixProd_symm (μ : Measure β) (ν : Measure γ) [SigmaFinite μ]
    [SigmaFinite ν] :
    MeasurePreserving
      (fun (P : (a → b → β) × (a → b → γ)) (i : a) (j : b) => (P.1 i j, P.2 i j))
      ((Measure.pi fun _ : a => Measure.pi fun _ : b => μ).prod
        (Measure.pi fun _ : a => Measure.pi fun _ : b => ν))
      (Measure.pi fun _ : a => Measure.pi fun _ : b => μ.prod ν) := by
  let e : (a → b → β × γ) ≃ᵐ (a → b → β) × (a → b → γ) :=
    (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.arrowProdEquivProdArrow β γ b).trans
      (MeasurableEquiv.arrowProdEquivProdArrow (b → β) (b → γ) a)
  have he : MeasurePreserving e (Measure.pi fun _ : a => Measure.pi fun _ : b => μ.prod ν)
      ((Measure.pi fun _ : a => Measure.pi fun _ : b => μ).prod
        (Measure.pi fun _ : a => Measure.pi fun _ : b => ν)) := by
    convert measurePreserving_matrixProd (a := a) (b := b) μ ν using 1
    funext M
    rfl
  convert he.symm using 1
  funext P
  rfl

/-- Moving the index of a family of matrices inside: `(f v i j) ↦ (i, j ↦ (v ↦ f v i j))`. -/
theorem measurePreserving_transpose (k m : ℕ) (μ : a → Measure β) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (fun (f : a → Fin k → Fin m → β) (i : Fin k) (j : Fin m) (v : a) => f v i j)
      (Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μ v)
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => Measure.pi fun v => μ v) := by
  have h1 := measurePreserving_swap (a := a) (b := Fin k) (β := Fin m → β)
    (fun v _ => Measure.pi fun _ : Fin m => μ v)
  have h2 := measurePreserving_pi (fun _ : Fin k => Measure.pi fun v => Measure.pi fun _ : Fin m => μ v)
    (fun _ : Fin k => Measure.pi fun _ : Fin m => Measure.pi fun v => μ v)
    (fun _ => measurePreserving_swap (a := a) (b := Fin m) (β := β) (fun v _ => μ v))
  exact h2.comp h1

/-- Rearranging a pair of families of matrices into a matrix of pairs of families. -/
theorem measurePreserving_rearrange (k m : ℕ) {c : Type*} [Fintype c] (μ : a → Measure β)
    (ν : c → Measure γ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving
      (fun (p : (a → Fin k → Fin m → β) × (c → Fin k → Fin m → γ)) (i : Fin k) (j : Fin m) =>
        ((fun v => p.1 v i j), (fun w => p.2 w i j)))
      ((Measure.pi fun v => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μ v).prod
        (Measure.pi fun w => Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => ν w))
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m =>
        (Measure.pi μ).prod (Measure.pi ν)) := by
  have h := (measurePreserving_transpose k m μ).prod (measurePreserving_transpose k m ν)
  exact (measurePreserving_matrixProd_symm (Measure.pi μ) (Measure.pi ν)).comp h

end Generic

end Langlands.Global.RankinSelbergGlobal.RectangleTate
