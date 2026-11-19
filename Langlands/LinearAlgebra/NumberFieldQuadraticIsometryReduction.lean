import Langlands.Global.LocalModularCharacter.HaarScaleNorm
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryStatement
import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyStatement
import Langlands.LinearAlgebra.QuadraticWittCancellation
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Reduction of local-to-global quadratic isometry to isotropy -/

noncomputable section

universe u

open QuadraticMap
open scoped TensorProduct

namespace Langlands

/-- The local-to-global isotropy theorem implies the local-to-global isometry theorem. -/
def NumberFieldQuadraticIsometryReductionStatement : Prop :=
  NumberFieldQuadraticIsotropyStatement.{u} → NumberFieldQuadraticIsometryStatement.{u}

namespace QuadraticIsometryReduction

section ScalarExtension

variable {F V W : Type*} [Field F] [Invertible (2 : F)]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  (A : Type*) [CommRing A] [Algebra F A]

private def extendIsometry {q : QuadraticForm F V} {r : QuadraticForm F W}
    (e : q.IsometryEquiv r) : (q.baseChange A).IsometryEquiv (r.baseChange A) := by
  let f := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e.toLinearEquiv
  refine ⟨f, fun z => ?_⟩
  have h : (r.baseChange A).comp f.toLinearMap = q.baseChange A := by
    apply baseChange_ext
    intro x
    change (r.baseChange A) (f (1 ⊗ₜ[F] x)) = (q.baseChange A) (1 ⊗ₜ[F] x)
    simp [f, e.map_app]
  exact DFunLike.congr_fun h z

private def extendLineProduct (a : F) (q : QuadraticForm F V) :
    (QuadraticForm.baseChange A ((a • (QuadraticMap.sq : QuadraticForm F F)).prod q)).IsometryEquiv
      ((algebraMap F A a • (QuadraticMap.sq : QuadraticForm A A)).prod (q.baseChange A)) := by
  let f := (TensorProduct.prodRight F A A F V).trans
    ((TensorProduct.AlgebraTensorModule.rid F A A).prodCongr
      (LinearEquiv.refl A (A ⊗[F] V)))
  let r := (algebraMap F A a • (QuadraticMap.sq : QuadraticForm A A)).prod (q.baseChange A)
  refine ⟨f, fun z => ?_⟩
  have h : r.comp f.toLinearMap =
      QuadraticForm.baseChange A ((a • (QuadraticMap.sq : QuadraticForm F F)).prod q) := by
    apply baseChange_ext
    rintro ⟨t, x⟩
    change r (f (1 ⊗ₜ[F] (t, x))) =
      (QuadraticForm.baseChange A ((a • (QuadraticMap.sq : QuadraticForm F F)).prod q)) (1 ⊗ₜ[F] (t, x))
    simp [r, f, Algebra.smul_def]
  exact DFunLike.congr_fun h z

end ScalarExtension

section OrthogonalLine

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem polarBilin_isRefl (q : QuadraticForm F V) : q.polarBilin.IsRefl :=
  fun x y h => (polar_comm q y x).trans h

private theorem lineProduct_nondegenerate [Invertible (2 : F)]
    (a : F) (ha : a ≠ 0) {q : QuadraticForm F V} (hq : q.polarBilin.Nondegenerate) :
    ((a • (QuadraticMap.sq : QuadraticForm F F)).prod q).polarBilin.Nondegenerate := by
  let line : QuadraticForm F F := a • QuadraticMap.sq
  apply (polarBilin_isRefl (line.prod q)).nondegenerate_iff_separatingLeft.mpr
  rintro ⟨t, x⟩ h
  have ht : polar line t 1 = 0 := by
    simpa only [polarBilin_apply_apply, polar_prod, polar_zero_right, add_zero] using h (1, 0)
  rw [← show t • (1 : F) = t by simp, polar_smul_left, polar_self] at ht
  have hmul : t * (2 * a) = 0 := by simpa [line, two_smul, two_mul] using ht
  have ht₀ := (mul_eq_zero.mp hmul).resolve_right (mul_ne_zero (Invertible.ne_zero _) ha)
  have hx : x = 0 := hq.1 x fun y => by
    simpa only [polarBilin_apply_apply, polar_prod, polar_zero_right, zero_add] using h (0, y)
  exact Prod.ext ht₀ hx

private theorem represents_of_isotropic_lineProduct (q : QuadraticForm F V)
    (hq : q.polarBilin.Nondegenerate) (a : F)
    (h : ¬ ((-a • (QuadraticMap.sq : QuadraticForm F F)).prod q).Anisotropic) :
    ∃ y, q y = a := by
  obtain ⟨⟨t, y⟩, hne, hz⟩ := (not_anisotropic_iff_exists _).mp h
  change (-a) * (t * t) + q y = 0 at hz
  have heq : q y = a * (t * t) := by linear_combination hz
  by_cases ht : t = 0
  · have hy : y ≠ 0 := fun h => hne (Prod.ext ht h)
    have hy₀ : q y = 0 := by simp [heq, ht]
    obtain ⟨z, hz⟩ : ∃ z, polar q y z ≠ 0 := by
      by_contra! hzero
      exact hy (hq.1 y hzero)
    refine ⟨z + ((a - q z) / polar q y z) • y, ?_⟩
    rw [QuadraticMap.map_add q, q.map_smul, polar_smul_right, polar_comm q z y, hy₀,
      smul_zero, add_zero, smul_eq_mul, div_mul_cancel₀ _ hz]
    ring
  · refine ⟨t⁻¹ • y, ?_⟩
    rw [q.map_smul, heq, smul_eq_mul]
    field_simp

private abbrev lineComplement (q : QuadraticForm F V) (x : V) : Submodule F V :=
  LinearMap.BilinForm.orthogonal q.polarBilin (F ∙ x)

variable [Invertible (2 : F)]

private theorem polar_self_ne_zero (q : QuadraticForm F V) (x : V) (hx : q x ≠ 0) :
    q.polarBilin x x ≠ 0 := by
  rw [polarBilin_apply_apply, polar_self, two_smul, ← two_mul]
  exact mul_ne_zero (Invertible.ne_zero _) hx

private theorem lineComplement_nondegenerate (q : QuadraticForm F V) (x : V) (hx : q x ≠ 0)
    (hq : q.polarBilin.Nondegenerate) :
    (q.restrict (lineComplement q x)).polarBilin.Nondegenerate :=
  LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
    q.polarBilin hq (polarBilin_isRefl q) (polar_self_ne_zero q x hx)

private def splitLine (q : QuadraticForm F V) (x : V) (hx : q x ≠ 0) :
    ((q x • (QuadraticMap.sq : QuadraticForm F F)).prod
      (q.restrict (lineComplement q x))).IsometryEquiv q := by
  let complement := lineComplement q x
  have hx₀ : x ≠ 0 := fun h => hx (h.symm ▸ map_zero q)
  let e := (LinearEquiv.toSpanNonzeroSingleton F V x hx₀).prodCongr
    (LinearEquiv.refl F complement)
  let f := (F ∙ x).prodEquivOfIsCompl complement
    (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (polar_self_ne_zero q x hx))
  refine ⟨e.trans f, ?_⟩
  rintro ⟨t, y⟩
  have hy : polar q x y = 0 := y.property x (Submodule.mem_span_singleton_self x)
  change q (t • x + (y : V)) = q x * (t * t) + q y
  rw [QuadraticMap.map_add q, q.map_smul, polar_smul_left, hy, smul_zero, add_zero,
    smul_eq_mul, mul_comm (t * t)]

private theorem finrank_lineComplement [FiniteDimensional F V]
    (q : QuadraticForm F V) (x : V) (hx : q x ≠ 0) {n : ℕ}
    (hdim : Module.finrank F V = n + 1) :
    Module.finrank F (lineComplement q x) = n := by
  have h := (splitLine q x hx).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, hdim] at h
  omega

end OrthogonalLine

section NumberField

variable {F : Type u} [Field F] [NumberField F]

local instance : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)

private theorem represents_of_local_equivalent (isotropy : NumberFieldQuadraticIsotropyStatement.{u})
    {V W : Type u} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (q : QuadraticForm F V) (r : QuadraticForm F W)
    (hr : r.polarBilin.Nondegenerate)
    (hloc : ∀ v : Global.Place F, (q.baseChange (Global.placeCompletion F v)).Equivalent
      (r.baseChange (Global.placeCompletion F v)))
    (x : V) (hx : q x ≠ 0) : ∃ y, r y = q x := by
  apply represents_of_isotropic_lineProduct r hr
  apply isotropy F (F × W) _ (lineProduct_nondegenerate (-q x) (neg_ne_zero.mpr hx) hr)
  intro v
  let A := Global.placeCompletion F v
  let : Field A := (Global.placeCompletion.isField F v).toField
  obtain ⟨e⟩ := hloc v
  let f := (extendLineProduct A (-q x) r).symm
  let y : A × (A ⊗[F] W) := (1, e (1 ⊗ₜ[F] x))
  apply (not_anisotropic_iff_exists _).mpr
  refine ⟨f y, ?_, (f.map_app y).trans ?_⟩
  · intro h
    have hy : y = 0 := f.toLinearEquiv.injective (h.trans (map_zero f).symm)
    exact one_ne_zero (congrArg Prod.fst hy)
  · change algebraMap F A (-q x) * (1 * 1) + (r.baseChange A) (e (1 ⊗ₜ[F] x)) = 0
    rw [e.map_app, QuadraticForm.baseChange_tmul]
    simp [A, Algebra.smul_def]

private theorem equivalent_of_local_equivalent (isotropy : NumberFieldQuadraticIsotropyStatement.{u})
    (n : ℕ) :
    ∀ (V W : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (q : QuadraticForm F V) (r : QuadraticForm F W),
      Module.finrank F V = n → Module.finrank F W = n →
      q.polarBilin.Nondegenerate → r.polarBilin.Nondegenerate →
      (∀ v : Global.Place F, (q.baseChange (Global.placeCompletion F v)).Equivalent
        (r.baseChange (Global.placeCompletion F v))) →
      q.Equivalent r := by
  induction n with
  | zero =>
    intro V W _ _ _ _ _ _ q r hV hW _ _ _
    let : Subsingleton V := Module.finrank_zero_iff.mp hV
    let : Subsingleton W := Module.finrank_zero_iff.mp hW
    refine ⟨⟨LinearEquiv.ofSubsingleton V W, fun x => ?_⟩⟩
    change r 0 = q x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  | succ n ih =>
    intro V W _ _ _ _ _ _ q r hV hW hq hr hloc
    have hpos : 0 < Module.finrank F V := by rw [hV]; exact Nat.succ_pos n
    let : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨x, hx⟩ : ∃ x, q x ≠ 0 := by
      by_contra! h
      apply LinearMap.BilinForm.Nondegenerate.ne_zero hq
      exact LinearMap.ext₂ fun x y => by simp [polarBilin_apply_apply, polar, h]
    obtain ⟨y, hy⟩ := represents_of_local_equivalent isotropy q r hr hloc x hx
    have hy₀ : r y ≠ 0 := fun h => hx (hy.symm.trans h)
    let q' := q.restrict (lineComplement q x)
    let r' := r.restrict (lineComplement r y)
    let e₁ := splitLine q x hx
    let e₂ : ((q x • (QuadraticMap.sq : QuadraticForm F F)).prod r').IsometryEquiv r := by
      rw [← hy]
      exact splitLine r y hy₀
    have hrest : q'.Equivalent r' := by
      apply ih _ _ q' r' (finrank_lineComplement q x hx hV) (finrank_lineComplement r y hy₀ hW)
        (lineComplement_nondegenerate q x hx hq) (lineComplement_nondegenerate r y hy₀ hr)
      intro v
      let A := Global.placeCompletion F v
      let : Field A := (Global.placeCompletion.isField F v).toField
      let : Invertible (2 : A) :=
        (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
      obtain ⟨e⟩ := hloc v
      let f₁ := (extendLineProduct A (q x) q').symm.trans (extendIsometry A e₁)
      let f₂ := (extendLineProduct A (q x) r').symm.trans (extendIsometry A e₂)
      have ha : algebraMap F A (q x) ≠ 0 := fun h => hx ((algebraMap F A).injective (h.trans (map_zero _).symm))
      exact quadraticForm_equivalent_of_prod_smul_sq _ ha ⟨(f₁.trans e).trans f₂.symm⟩
    obtain ⟨e⟩ := hrest
    exact ⟨(e₁.symm.trans (QuadraticMap.IsometryEquiv.prod
      (QuadraticMap.IsometryEquiv.refl _) e)).trans e₂⟩

end NumberField

end QuadraticIsometryReduction

/-- Nondegenerate quadratic isometry over number fields follows from isotropy over the
same number fields and completions. -/
theorem numberFieldQuadraticIsometry_of_isotropy :
    NumberFieldQuadraticIsometryReductionStatement.{u} := by
  intro isotropy F _ _ n q r hq hr hloc
  exact QuadraticIsometryReduction.equivalent_of_local_equivalent isotropy n _ _ q r
    (Module.finrank_fin_fun F) (Module.finrank_fin_fun F) hq hr hloc

end Langlands
