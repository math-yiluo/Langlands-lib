import Langlands.Geometry.FormalGroup.OrderAction

/-! # Tangent maps of finite-coordinate formal groups -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type u} [CommRing R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

namespace CoordinateMap

omit [Finite τ] in
private theorem homogeneous_zero (g : MvPowerSeries τ R) :
    g.homogeneousComponent 0 = C g.constantCoeff := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp [coeff_homogeneousComponent]
  · simp [coeff_homogeneousComponent, Finsupp.degree_eq_zero_iff, hd, coeff_C]

omit [Finite τ] in
private theorem homogeneous_one [Fintype τ] (g : MvPowerSeries τ R) :
    g.homogeneousComponent 1 =
      ∑ i, C (coeff (Finsupp.single i 1) g) * X i := by
  classical
  ext d
  by_cases hd : d.degree = 1
  · have hm : d ∈ Set.range (fun i : τ => Finsupp.single i 1) := by
      rwa [Finsupp.range_single_one]
    obtain ⟨i, rfl⟩ := hm
    simp [coeff_homogeneousComponent, coeff_C_mul, coeff_index_single_X]
  · have hdi (i : τ) : d ≠ Finsupp.single i 1 := by
      intro h
      exact hd (h ▸ Finsupp.degree_single i 1)
    simp [coeff_homogeneousComponent, hd, coeff_C_mul, coeff_X, hdi]

/-- The linear coefficient of a substitution with zero constant terms. -/
theorem coeff_subst_linear [Fintype τ] (f : CoordinateMap R σ τ)
    (g : MvPowerSeries τ R) (j : σ) :
    coeff (Finsupp.single j 1) (subst f.series g) =
      ∑ i, coeff (Finsupp.single i 1) g * f.linearCoeff i j := by
  classical
  have h := congrArg (fun p : MvPolynomial σ R => p.coeff (Finsupp.single j 1))
    (truncTotal_subst_eq_truncTotal_subst_sum
      (k := 2) f.hasSubst f.constantCoeff_eq_zero (f := g))
  simp only [coeff_truncTotal, Finsupp.degree_single, Nat.one_lt_ofNat] at h
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, homogeneous_zero, homogeneous_one] at h
  simp only [← substAlgHom_apply f.hasSubst, map_add, map_sum, map_mul,
    substAlgHom_X] at h
  simpa [substAlgHom_apply, subst_C, coeff_C, coeff_C_mul,
    linearCoeff] using h

omit [Finite υ] in
/-- The chain rule for linear coefficient matrices. -/
theorem linearCoeff_comp [Fintype τ] (g : CoordinateMap R τ υ)
    (f : CoordinateMap R σ τ) (i : υ) (j : σ) :
    (g.comp f).linearCoeff i j = ∑ k, g.linearCoeff i k * f.linearCoeff k j :=
  coeff_subst_linear f (g.series i) j

omit [Finite τ] in
/-- The tangent map acts by its actual linear coefficient matrix. -/
theorem linearPart_apply [Fintype σ] (f : CoordinateMap R σ τ) (x : σ → R) (i : τ) :
    f.linearPart x i = ∑ j, f.linearCoeff i j * x j := by
  classical
  simp only [linearPart, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

omit [Finite τ] in
@[simp]
theorem linearPart_zero : (zero (R := R) (σ := σ) (τ := τ)).linearPart = 0 := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply LinearMap.ext
  intro x
  funext i
  simp [linearPart_apply, linearCoeff]

@[simp]
theorem linearPart_id : (id (R := R) (σ := σ)).linearPart = LinearMap.id := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply LinearMap.ext
  intro x
  funext i
  simp [linearPart_apply, linearCoeff, coeff_index_single_X]

omit [Finite υ] in
/-- Differentiation preserves actual formal composition. -/
theorem linearPart_comp (g : CoordinateMap R τ υ) (f : CoordinateMap R σ τ) :
    (g.comp f).linearPart = g.linearPart.comp f.linearPart := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype τ := Fintype.ofFinite τ
  have h : (g.comp f).linearCoeff = g.linearCoeff * f.linearCoeff := by
    funext i j
    exact linearCoeff_comp g f i j
  simpa only [linearPart, h] using
    (Matrix.mulVecLin_mul g.linearCoeff f.linearCoeff)

omit [Finite τ] [Finite υ] in
/-- Pairing formal maps pairs their tangent vectors. -/
theorem linearPart_pair (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ)
    (x : σ → R) :
    (f.pair g).linearPart x = Sum.elim (f.linearPart x) (g.linearPart x) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  funext i
  cases i <;> simp [linearPart_apply, linearCoeff]

end CoordinateMap

namespace CommLaw

variable (G : CommLaw R σ)

/-- The tangent of formal addition is ordinary vector addition. -/
theorem linearPart_addition (x y : σ → R) :
    G.addition.linearPart (Sum.elim x y) = x + y := by
  have hx := congrArg (fun f : CoordinateMap R σ σ => f.linearPart x) G.add_zero
  have hy := congrArg (fun f : CoordinateMap R σ σ => f.linearPart y) G.zero_add
  simp only [CoordinateMap.linearPart_comp, LinearMap.comp_apply,
    CoordinateMap.linearPart_pair, CoordinateMap.linearPart_id,
    CoordinateMap.linearPart_zero, LinearMap.id_apply, LinearMap.zero_apply] at hx hy
  have h : Sum.elim x y = Sum.elim x (0 : σ → R) + Sum.elim (0 : σ → R) y := by
    funext i
    cases i <;> simp
  rw [h, _root_.map_add, hx, hy]

namespace Hom

variable {G : CommLaw R σ} {H : CommLaw R τ} {I : CommLaw R υ}

/-- The tangent map of an actual formal group homomorphism. -/
def tangent (f : Hom G H) : (σ → R) →ₗ[R] (τ → R) :=
  f.toCoordinateMap.linearPart

@[simp]
theorem tangent_id : (id G).tangent = LinearMap.id := CoordinateMap.linearPart_id

@[simp]
theorem tangent_zero : (0 : Hom G H).tangent = 0 := CoordinateMap.linearPart_zero

@[simp]
theorem tangent_comp (g : Hom H I) (f : Hom G H) :
    (g.comp f).tangent = g.tangent.comp f.tangent :=
  CoordinateMap.linearPart_comp _ _

@[simp]
theorem tangent_add (f g : Hom G H) : (f + g).tangent = f.tangent + g.tangent := by
  apply LinearMap.ext
  intro x
  change (H.addition.comp (f.toCoordinateMap.pair g.toCoordinateMap)).linearPart x = _
  rw [CoordinateMap.linearPart_comp, LinearMap.comp_apply, CoordinateMap.linearPart_pair,
    H.linearPart_addition]
  rfl

/-- Differentiation is additive in a formal homomorphism. -/
def tangentAddHom : Hom G H →+ ((σ → R) →ₗ[R] (τ → R)) where
  toFun := tangent
  map_zero' := tangent_zero
  map_add' := tangent_add

/-- Differentiation of endomorphisms is a unital ring homomorphism. -/
def tangentEnd (G : CommLaw R σ) : Hom G G →+* Module.End R (σ → R) where
  toFun := tangent
  map_zero' := tangent_zero
  map_add' := tangent_add
  map_one' := tangent_id
  map_mul' := tangent_comp

end Hom

namespace Iso

variable {G : CommLaw R σ} {H : CommLaw R τ}

/-- Inverse formal homomorphisms differentiate to inverse linear maps. -/
def tangent (f : Iso G H) : (σ → R) ≃ₗ[R] (τ → R) where
  toLinearMap := f.hom.tangent
  invFun := f.inv.tangent
  left_inv x := by
    change (f.inv.tangent.comp f.hom.tangent) x = x
    rw [← Hom.tangent_comp, f.inv_hom, Hom.tangent_id, LinearMap.id_apply]
  right_inv x := by
    change (f.hom.tangent.comp f.inv.tangent) x = x
    rw [← Hom.tangent_comp, f.hom_inv, Hom.tangent_id, LinearMap.id_apply]

end Iso

end CommLaw

namespace ModuleLaw

variable {O : Type v} [CommRing O] [Algebra O R]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Hom

/-- The tangent map obtained from the underlying formal homomorphism. -/
def tangent (f : Hom M N) : (σ → R) →ₗ[R] (τ → R) := f.toHom.tangent

@[simp]
theorem tangent_id : (id M).tangent = LinearMap.id := CommLaw.Hom.tangent_id

@[simp]
theorem tangent_zero : (0 : Hom M N).tangent = 0 := CommLaw.Hom.tangent_zero

@[simp]
theorem tangent_add (f g : Hom M N) : (f + g).tangent = f.tangent + g.tangent :=
  CommLaw.Hom.tangent_add _ _

@[simp]
theorem tangent_comp (g : Hom N P) (f : Hom M N) :
    (g.comp f).tangent = g.tangent.comp f.tangent := CommLaw.Hom.tangent_comp _ _

@[simp]
theorem tangent_smul (a : O) (f : Hom M N) : (a • f).tangent = a • f.tangent := by
  apply LinearMap.ext
  intro x
  change ((N.action a).comp f.toHom).tangent x = _
  rw [CommLaw.Hom.tangent_comp, LinearMap.comp_apply]
  change (N.action a).toCoordinateMap.linearPart (f.tangent x) = a • f.tangent x
  rw [N.action_on_tangent, algebraMap_smul]

/-- Tangent maps depend O-linearly on the actual formal homomorphism. -/
def tangentLinear : Hom M N →ₗ[O] ((σ → R) →ₗ[R] (τ → R)) where
  toFun := tangent
  map_add' := tangent_add
  map_smul' := tangent_smul

/-- Differentiation on formal O-linear endomorphisms preserves their ring. -/
def tangentEnd (M : ModuleLaw O R σ) : Hom M M →+* Module.End R (σ → R) where
  toFun := tangent
  map_zero' := tangent_zero
  map_add' := tangent_add
  map_one' := tangent_id
  map_mul' := tangent_comp

end Hom

namespace Iso

/-- An isomorphism of formal O-modules induces an R-linear tangent equivalence. -/
def tangent (f : Iso M N) : (σ → R) ≃ₗ[R] (τ → R) where
  toLinearMap := f.hom.tangent
  invFun := f.inv.tangent
  left_inv x := by
    change (f.inv.tangent.comp f.hom.tangent) x = x
    rw [← Hom.tangent_comp, f.inv_hom, Hom.tangent_id, LinearMap.id_apply]
  right_inv x := by
    change (f.hom.tangent.comp f.inv.tangent) x = x
    rw [← Hom.tangent_comp, f.hom_inv, Hom.tangent_id, LinearMap.id_apply]

end Iso

namespace OrderAction

variable {A : Type w} [Ring A] [Algebra O A]
variable (E : OrderAction A M) (E' : OrderAction A N)

/-- The representation on coordinate tangent vectors is induced by the formal action. -/
def tangent : A →+* Module.End R (σ → R) := (Hom.tangentEnd M).comp E.action

@[simp]
theorem tangent_apply (a : A) : E.tangent a = (E.action a).tangent := rfl

/-- The tangent representation restricts to the natural O-action. -/
theorem tangent_scalar (a : O) (x : σ → R) :
    E.tangent (algebraMap O A a) x = algebraMap O R a • x := by
  change (E.action (algebraMap O A a)).toHom.toCoordinateMap.linearPart x = _
  rw [E.extends_scalars]
  exact M.action_on_tangent a x

namespace Hom

variable {E E'}

/-- The actual derivative of an order-linear map intertwines tangent representations. -/
theorem tangent_commutes (f : Hom E E') (a : A) :
    f.val.tangent.comp (E.tangent a) = (E'.tangent a).comp f.val.tangent := by
  have h := congrArg ModuleLaw.Hom.tangent (f.commutes a)
  simpa only [ModuleLaw.Hom.tangent_comp, tangent_apply] using h

end Hom

end OrderAction

end ModuleLaw

end Langlands.FormalGroup
