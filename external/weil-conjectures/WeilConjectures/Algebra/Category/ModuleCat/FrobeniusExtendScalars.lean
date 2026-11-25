/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.BigOperators
public import WeilConjectures.Algebra.Category.ModuleCat.CoextendScalarsAdjunction

/-!
# Restriction of scalars is left adjoint to extension of scalars for Frobenius data

Let `f : A →+* B` be a morphism of commutative rings. *Frobenius data* for `f`
(`ModuleCat.FrobeniusData`) consist of an additive trace `t : B → A` with
`t(f(r) x) = r t(x)` and two finite families `(bᵢ)`, `(cᵢ)` of elements of `B` such that
`x = ∑ᵢ f(t(x cᵢ)) bᵢ = ∑ᵢ f(t(x bᵢ)) cᵢ` for every `x ∈ B`. Then restriction of scalars
along `f` is left adjoint to extension of scalars (`ModuleCat.FrobeniusData.adjunction`),
with unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n` and counit `s ⊗ m ↦ t(s) m`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped ChangeOfRings

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Frobenius data for a ring morphism `f : A →+* B`: an `A`-linear trace `B → A` and two finite
families `bᵢ`, `cᵢ` in `B` with `x = ∑ᵢ f(t(x cᵢ)) bᵢ = ∑ᵢ f(t(x bᵢ)) cᵢ`. -/
structure FrobeniusData (f : A →+* B) (d : ℕ) where
  /-- The trace. -/
  trace : B →+ A
  trace_mul (r : A) (x : B) : trace (f r * x) = r * trace x
  /-- The first family. -/
  basis : Fin d → B
  /-- The second family. -/
  dual : Fin d → B
  sum_trace_mul_dual (x : B) : ∑ i, f (trace (x * dual i)) * basis i = x
  sum_trace_mul_basis (x : B) : ∑ i, f (trace (x * basis i)) * dual i = x

namespace FrobeniusData

variable {f : A →+* B} {d : ℕ} (D : FrobeniusData f d)

variable (f) in
/-- The pure tensor `b ⊗ m` in the extension of scalars of `M`. -/
def tmulExt (M : ModuleCat.{u} A) (b : B) (m : M) : (extendScalars f).obj M :=
  (TensorProduct.mk A ((restrictScalars f).obj (of B B)) M b m :
    TensorProduct A ((restrictScalars f).obj (of B B)) M)

lemma tmulExt_sum_left (M : ModuleCat.{u} A) (b : Fin d → B) (m : M) :
    tmulExt f M (∑ i, b i) m = ∑ i, tmulExt f M (b i) m :=
  LinearMap.congr_fun (map_sum (TensorProduct.mk A ((restrictScalars f).obj (of B B)) M) _ _)
    m |>.trans (LinearMap.sum_apply _ _ _)

lemma tmulExt_mul_left (M : ModuleCat.{u} A) (r : A) (b : B) (m : M) :
    tmulExt f M (f r * b) m = tmulExt f M b (r • m) :=
  TensorProduct.smul_tmul (R := A) (M := (restrictScalars f).obj (of B B)) (N := M) r b m

lemma smul_tmulExt (M : ModuleCat.{u} A) (s b : B) (m : M) :
    s • tmulExt f M b m = tmulExt f M (s * b) m := rfl

variable (f) in
/-- The pure tensor `b ⊗ n` in the extension of scalars of the restriction of scalars of `N`. -/
def tmulRes (N : ModuleCat.{u} B) (b : B) (n : N) :
    (extendScalars f).obj ((restrictScalars f).obj N) :=
  (TensorProduct.mk A ((restrictScalars f).obj (of B B)) ((restrictScalars f).obj N) b n :
    TensorProduct A ((restrictScalars f).obj (of B B)) ((restrictScalars f).obj N))

lemma tmulRes_eq (N : ModuleCat.{u} B) (b : B) (n : N) :
    tmulRes f N b n = b ⊗ₜ[A,f] (id n : (restrictScalars f).obj N) := rfl

lemma tmulRes_add_right (N : ModuleCat.{u} B) (b : B) (n n' : N) :
    tmulRes f N b (n + n') = tmulRes f N b n + tmulRes f N b n' :=
  (TensorProduct.mk A ((restrictScalars f).obj (of B B)) ((restrictScalars f).obj N) b).map_add
    n n'

lemma tmulRes_sum_left (N : ModuleCat.{u} B) (b : Fin d → B) (n : N) :
    tmulRes f N (∑ i, b i) n = ∑ i, tmulRes f N (b i) n :=
  LinearMap.congr_fun (map_sum (TensorProduct.mk A ((restrictScalars f).obj (of B B))
    ((restrictScalars f).obj N)) _ _) n |>.trans (LinearMap.sum_apply _ _ _)

lemma tmulRes_sum_right (N : ModuleCat.{u} B) (b : B) (n : Fin d → N) :
    tmulRes f N b (∑ i, n i) = ∑ i, tmulRes f N b (n i) :=
  map_sum (TensorProduct.mk A ((restrictScalars f).obj (of B B))
    ((restrictScalars f).obj N) b) _ _

lemma tmulRes_mul_left (N : ModuleCat.{u} B) (r : A) (b : B) (n : N) :
    tmulRes f N (f r * b) n = tmulRes f N b (f r • n) :=
  TensorProduct.smul_tmul (R := A) (M := (restrictScalars f).obj (of B B))
    (N := (restrictScalars f).obj N) r b n

lemma smul_tmulRes (N : ModuleCat.{u} B) (s b : B) (n : N) :
    s • tmulRes f N b n = tmulRes f N (s * b) n := rfl

/-- The unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n`. -/
def unitApp (N : ModuleCat.{u} B) : N ⟶ (extendScalars f).obj ((restrictScalars f).obj N) :=
  ofHom (X := N) (Y := (extendScalars f).obj ((restrictScalars f).obj N))
    { toFun n := ∑ i, tmulRes f N (D.basis i) (D.dual i • n)
      map_add' n n' := by
        simp only [smul_add, tmulRes_add_right, Finset.sum_add_distrib]
      map_smul' s n := by
        rw [RingHom.id_apply]
        erw [Finset.smul_sum]
        simp only [smul_tmulRes]
        symm
        calc ∑ i, tmulRes f N (s * D.basis i) (D.dual i • n)
            = ∑ i, ∑ j, tmulRes f N (D.basis j)
                (f (D.trace (s * D.dual j * D.basis i)) • D.dual i • n) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              conv_lhs => rw [← D.sum_trace_mul_dual (s * D.basis i)]
              rw [tmulRes_sum_left]
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [tmulRes_mul_left, mul_right_comm]
          _ = ∑ j, tmulRes f N (D.basis j) ((s * D.dual j) • n) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [← tmulRes_sum_right]
              congr 1
              conv_rhs => rw [← D.sum_trace_mul_basis (s * D.dual j)]
              rw [Finset.sum_smul]
              simp only [mul_smul]
          _ = ∑ i, tmulRes f N (D.basis i) (D.dual i • s • n) := by
              simp only [mul_smul, smul_comm s]
      }

lemma unitApp_apply (N : ModuleCat.{u} B) (n : N) :
    D.unitApp N n = ∑ i, tmulRes f N (D.basis i) (D.dual i • n) := rfl

/-- The bilinear map `(s, m) ↦ t(s) m`. -/
def traceSMul (M : ModuleCat.{u} A) :
    (restrictScalars f).obj (of B B) →ₗ[A] M →ₗ[A] M :=
  LinearMap.mk₂ A (fun (s : B) (m : M) ↦ D.trace s • m)
    (fun s s' m ↦ (congrArg (· • m) (D.trace.map_add s s')).trans (add_smul _ _ _))
    (fun r s m ↦ (congrArg (· • m) (D.trace_mul r s)).trans (mul_smul _ _ _))
    (fun _ _ _ ↦ smul_add _ _ _)
    (fun _ _ _ ↦ smul_comm _ _ _)

/-- The counit `s ⊗ m ↦ t(s) m`. -/
def counitApp (M : ModuleCat.{u} A) :
    (restrictScalars f).obj ((extendScalars f).obj M) ⟶ M :=
  ofHom (X := (restrictScalars f).obj ((extendScalars f).obj M)) (Y := M)
    { toFun z := TensorProduct.lift (D.traceSMul M) z
      map_add' z z' := map_add _ _ _
      map_smul' r z := by
        induction z using TensorProduct.inductionOn with
        | add z z' hz hz' =>
          erw [smul_add, map_add, map_add, hz, hz', smul_add]
        | tmul s m => exact (congrArg (· • m) (D.trace_mul r s)).trans (mul_smul _ _ _) }

lemma counitApp_tmulExt (M : ModuleCat.{u} A) (s : B) (m : M) :
    D.counitApp M (tmulExt f M s m) = D.trace s • m := rfl

lemma counitApp_tmulRes (N : ModuleCat.{u} B) (s : B) (n : N) :
    D.counitApp ((restrictScalars f).obj N) (tmulRes f N s n) = f (D.trace s) • n := rfl

lemma counitApp_unitApp (N : ModuleCat.{u} B) (n : N) :
    D.counitApp ((restrictScalars f).obj N) (D.unitApp N n) = n := by
  rw [unitApp_apply]
  erw [map_sum]
  simp only [counitApp_tmulRes, ← mul_smul]
  conv_rhs => rw [← one_smul B n, ← D.sum_trace_mul_basis 1]
  simp only [one_mul, Finset.sum_smul]

/-- Restriction of scalars along a ring morphism with Frobenius data is left adjoint to extension
of scalars. -/
def adjunction : restrictScalars.{u} f ⊣ extendScalars.{u, u, u} f :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := D.unitApp
          naturality N N' g := by
            ext n
            change D.unitApp N' (g n) = (extendScalars f).map ((restrictScalars f).map g)
              (D.unitApp N n)
            rw [unitApp_apply, unitApp_apply, map_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [← map_smul]
            rfl }
      counit :=
        { app := D.counitApp
          naturality M M' h := by
            ext z
            change D.counitApp M' ((extendScalars f).map h z) = h (D.counitApp M z)
            induction z using TensorProduct.inductionOn with
            | add z z' hz hz' => erw [map_add, map_add, hz, hz', map_add, map_add]
            | tmul s m => exact (h.hom.map_smul _ m).symm }
      left_triangle := by
        ext N n
        exact D.counitApp_unitApp N n
      right_triangle := by
        ext M : 2
        apply ExtendScalars.hom_ext
        intro m
        change (extendScalars f).map (D.counitApp M) (D.unitApp _ (tmulExt f M 1 m)) =
          tmulExt f M 1 m
        rw [unitApp_apply]
        erw [map_sum]
        simp only [smul_tmulExt, mul_one]
        change ∑ i, tmulExt f M (D.basis i) (D.trace (D.dual i) • m) = _
        simp only [← tmulExt_mul_left, ← tmulExt_sum_left]
        congr 1
        conv_rhs => rw [← D.sum_trace_mul_dual 1]
        simp only [one_mul] }

lemma unitApp_naturality {N N' : ModuleCat.{u} B} (g : N ⟶ N') :
    g ≫ D.unitApp N' = D.unitApp N ≫ (extendScalars f).map ((restrictScalars f).map g) :=
  D.adjunction.unit.naturality g

lemma counitApp_naturality {M M' : ModuleCat.{u} A} (h : M ⟶ M') :
    (restrictScalars f).map ((extendScalars f).map h) ≫ D.counitApp M' = D.counitApp M ≫ h :=
  D.adjunction.counit.naturality h

lemma restrictScalars_map_unitApp_comp_counitApp (N : ModuleCat.{u} B) :
    (restrictScalars f).map (D.unitApp N) ≫ D.counitApp ((restrictScalars f).obj N) = 𝟙 _ :=
  D.adjunction.left_triangle_components N

lemma unitApp_comp_extendScalars_map_counitApp (M : ModuleCat.{u} A) :
    D.unitApp ((extendScalars f).obj M) ≫ (extendScalars f).map (D.counitApp M) = 𝟙 _ :=
  D.adjunction.right_triangle_components M

end FrobeniusData

section OfBasis

/-! ### Frobenius data obtained by base change of a Frobenius form

Let `A' → B'` be a finite free algebra with basis `b` and Frobenius form `t₀`, and let
`κA : A' → A`, `κB : B' → B` be compatible ring maps such that the `κB (b i)` form a basis of `B`
over `A`. Then `t(∑ᵢ f(rᵢ) κB(bᵢ)) = ∑ᵢ rᵢ κA(t₀ bᵢ)` defines Frobenius data for `f`. -/

variable {d : ℕ} {f : A →+* B} {A' B' : Type w} [CommRing A'] [CommRing B'] [Algebra A' B']
  (b : Module.Basis (Fin d) A' B') (κA : A' →+* A) (κB : B' →+* B)
  (hκ : ∀ a, f (κA a) = κB (algebraMap A' B' a))
  (hbij : Function.Bijective fun r : Fin d → A ↦ ∑ i, f (r i) * κB (b i))

namespace FrobeniusData

/-- The coordinates in the basis `κB (b i)`. -/
def coords (x : B) : Fin d → A := (Equiv.ofBijective _ hbij).symm x

include hbij in
lemma sum_coords (x : B) : ∑ i, f (coords b κB hbij x i) * κB (b i) = x :=
  (Equiv.ofBijective _ hbij).apply_symm_apply x

include hbij in
lemma coords_eq {x : B} {r : Fin d → A} (h : ∑ i, f (r i) * κB (b i) = x) :
    coords b κB hbij x = r := by
  rw [← h]
  exact (Equiv.ofBijective _ hbij).symm_apply_apply r

lemma coords_add (x y : B) :
    coords b κB hbij (x + y) = coords b κB hbij x + coords b κB hbij y := by
  refine coords_eq b κB hbij ?_
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, sum_coords]

lemma coords_mul (r : A) (x : B) :
    coords b κB hbij (f r * x) = fun i ↦ r * coords b κB hbij x i := by
  refine coords_eq b κB hbij ?_
  simp only [map_mul, mul_assoc, ← Finset.mul_sum, sum_coords]

include hκ in
lemma coords_map (y : B') :
    coords b κB hbij (κB y) = fun i ↦ κA (b.repr y i) := by
  refine coords_eq b κB hbij ?_
  simp only [hκ, ← map_mul, ← map_sum, ← Algebra.smul_def, b.sum_repr]

variable (t₀ : B' →ₗ[A'] A')

/-- The trace `∑ᵢ f(rᵢ) κB(bᵢ) ↦ ∑ᵢ rᵢ κA(t₀ bᵢ)`. -/
def ofBasisTrace : B →+ A where
  toFun x := ∑ i, coords b κB hbij x i * κA (t₀ (b i))
  map_zero' := by
    rw [coords_eq b κB hbij (r := 0) (by simp)]
    simp
  map_add' x y := by
    simp only [coords_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma ofBasisTrace_mul (r : A) (x : B) :
    ofBasisTrace b κA κB hbij t₀ (f r * x) = r * ofBasisTrace b κA κB hbij t₀ x := by
  simp only [ofBasisTrace, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coords_mul, Finset.mul_sum,
    mul_assoc]

include hκ in
lemma ofBasisTrace_map (y : B') :
    ofBasisTrace b κA κB hbij t₀ (κB y) = κA (t₀ y) := by
  simp only [ofBasisTrace, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coords_map b κA κB hκ hbij]
  conv_rhs => rw [← b.sum_repr y, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, map_mul]

include hκ in
lemma sum_ofBasisTrace_mul (g h : Fin d → B') (hgh : ∀ y : B', ∑ i, t₀ (y * g i) • h i = y)
    (x : B) : ∑ i, f (ofBasisTrace b κA κB hbij t₀ (x * κB (g i))) * κB (h i) = x := by
  have hx (i : Fin d) : ofBasisTrace b κA κB hbij t₀ (x * κB (g i)) =
      ∑ j, coords b κB hbij x j * κA (t₀ (b j * g i)) := by
    conv_lhs => rw [← sum_coords b κB hbij x]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, ← map_mul, ofBasisTrace_mul, ofBasisTrace_map b κA κB hκ hbij]
  conv_rhs => rw [← sum_coords b κB hbij x]
  simp only [hx, map_sum, map_mul, hκ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, ← Algebra.smul_def, hgh]

/-- Frobenius data for `f` obtained from a basis `b` and a Frobenius form `t₀` of `A' → B'`, along
compatible ring maps `κA`, `κB` such that the `κB (b i)` form a basis of `B` over `A`. -/
def ofBasis (ht₀ : Function.Bijective fun s : B' ↦ t₀ ∘ₗ LinearMap.mulLeft A' s) :
    FrobeniusData f d where
  trace := ofBasisTrace b κA κB hbij t₀
  trace_mul := ofBasisTrace_mul b κA κB hbij t₀
  basis i := κB (b i)
  dual i := κB (CoextendScalars.frobeniusDual b t₀ ht₀ i)
  sum_trace_mul_dual := sum_ofBasisTrace_mul b κA κB hκ hbij t₀ _ _ fun y ↦ by
    simp only [mul_comm y, CoextendScalars.apply_frobeniusDual_mul, Module.Basis.coord_apply,
      b.sum_repr]
  sum_trace_mul_basis := sum_ofBasisTrace_mul b κA κB hκ hbij t₀ _ _ fun y ↦ by
    simpa only [mul_comm y] using CoextendScalars.sum_smul_frobeniusDual b t₀ ht₀ y

end FrobeniusData

end OfBasis

end ModuleCat
