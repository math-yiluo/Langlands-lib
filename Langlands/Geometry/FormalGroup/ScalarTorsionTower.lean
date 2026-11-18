import Langlands.Geometry.FormalGroup.PiDivisible
import Mathlib.CategoryTheory.Category.Preorder

/-! # The scalar-power torsion system of a formal module -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable (M : ModuleLaw O R σ) (π : O)
variable {A : CommAlgCat.{v} R} {l m n : ℕ}

/-- An inclusion of scalar-power torsion subfunctors of the same formal module. -/
def torsionIncl (h : m ≤ n) :
    M.torsionPointFunctor.{u, v, v} (π ^ m) ⟶ M.torsionPointFunctor (π ^ n) :=
  (M.scalarHom (π ^ n)).kernelLift (M.scalarHom (π ^ m)).kernelι (by
    apply NatTrans.ext
    funext B
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (M.scalarHom (π ^ m)).kernelPoints B at x
    change (M.scalarHom (π ^ n)).onAlgebraPoints x.val = 0
    have hx := (M.mem_scalarKernel (π ^ m) B x.val).mp x.property
    rw [scalarHom_onAlgebraPoints, ← Nat.sub_add_cancel h, pow_add, mul_smul, hx, smul_zero])

@[simp]
theorem torsionIncl_app_val (h : m ≤ n) (x : (M.scalarHom (π ^ m)).kernelPoints A) :
    ((M.torsionIncl π h).app A x).val = x.val := rfl

theorem torsionIncl_app_injective (h : m ≤ n) :
    Function.Injective ((M.torsionIncl π h).app A) := by
  intro x y hxy
  have hval := congrArg (fun z : (M.scalarHom (π ^ n)).kernelPoints A => z.val) hxy
  exact Subtype.ext hval

/-- The transition from π^n-torsion to π^m-torsion acts by π^(n-m). -/
def torsionTransition (h : m ≤ n) :
    M.torsionPointFunctor.{u, v, v} (π ^ n) ⟶ M.torsionPointFunctor (π ^ m) :=
  (M.scalarHom (π ^ m)).kernelLift
    ((M.scalarHom (π ^ n)).kernelι ≫ (M.scalarHom (π ^ (n - m))).algebraPointNatTrans) (by
      apply NatTrans.ext
      funext B
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (M.scalarHom (π ^ n)).kernelPoints B at x
      change (M.scalarHom (π ^ m)).onAlgebraPoints
        ((M.scalarHom (π ^ (n - m))).onAlgebraPoints x.val) = 0
      rw [scalarHom_onAlgebraPoints, scalarHom_onAlgebraPoints, ← mul_smul, ← pow_add,
        Nat.add_comm m (n - m), Nat.sub_add_cancel h]
      exact (M.mem_scalarKernel (π ^ n) B x.val).mp x.property)

@[simp]
theorem torsionTransition_app_val (h : m ≤ n) (x : (M.scalarHom (π ^ n)).kernelPoints A) :
    ((M.torsionTransition π h).app A x).val = π ^ (n - m) • x.val :=
  M.scalarHom_onAlgebraPoints (π ^ (n - m)) A x.val

@[simp]
theorem torsionTransition_refl (n : ℕ) : M.torsionTransition π (le_refl n) = 𝟙 _ := by
  apply NatTrans.ext
  funext B
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((M.torsionTransition π (le_refl n)).app B x).val = x.val
  erw [torsionTransition_app_val]
  rw [Nat.sub_self, pow_zero, one_smul]

theorem torsionTransition_trans (h : l ≤ m) (k : m ≤ n) :
    M.torsionTransition π (h.trans k) = M.torsionTransition π k ≫ M.torsionTransition π h := by
  apply NatTrans.ext
  funext B
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((M.torsionTransition π (h.trans k)).app B x).val =
    ((M.torsionTransition π h).app B ((M.torsionTransition π k).app B x)).val
  have he : (m - l) + (n - m) = n - l := by omega
  erw [torsionTransition_app_val, torsionTransition_app_val, torsionTransition_app_val]
  rw [← mul_smul, ← pow_add, he]

/-- The inverse system of actual scalar-power torsion point functors. -/
def torsionTower : ℕᵒᵖ ⥤ (CommAlgCat.{v} R ⥤ ModuleCat.{v} O) where
  obj n := M.torsionPointFunctor (π ^ n.unop)
  map f := M.torsionTransition π (leOfHom f.unop)
  map_id n := M.torsionTransition_refl π n.unop
  map_comp f g := M.torsionTransition_trans π (leOfHom g.unop) (leOfHom f.unop)

/-- The kernel of multiplication by π^n on π^(m+n)-torsion is the included π^n-torsion. -/
theorem torsionTransition_add_eq_zero_iff (m n : ℕ)
    (x : (M.scalarHom (π ^ (m + n))).kernelPoints A) :
    (M.torsionTransition π (Nat.le_add_right m n)).app A x = 0 ↔
      ∃ y : (M.scalarHom (π ^ n)).kernelPoints A,
        (M.torsionIncl π (Nat.le_add_left n m)).app A y = x := by
  constructor
  · intro hx
    have hs := congrArg Subtype.val hx
    change ((M.torsionTransition π (Nat.le_add_right m n)).app A x).val = 0 at hs
    rw [torsionTransition_app_val, Nat.add_sub_cancel_left] at hs
    exact ⟨⟨x.val, (M.mem_scalarKernel (π ^ n) A x.val).mpr hs⟩, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change ((M.torsionTransition π (Nat.le_add_right m n)).app A
      ((M.torsionIncl π (Nat.le_add_left n m)).app A y)).val = 0
    erw [torsionTransition_app_val, torsionIncl_app_val]
    rw [Nat.add_sub_cancel_left]
    exact (M.mem_scalarKernel (π ^ n) A y.val).mp y.property

/-- The transition has local lifts after a faithfully flat finitely presented algebra map. -/
theorem IsPiDivisible.torsionTransition_locallySurjective {M : ModuleLaw O R σ} {π : O}
    (hM : M.IsPiDivisible π) (h : m ≤ n) (y : (M.scalarHom (π ^ m)).kernelPoints A) :
    ∃ (B : CommAlgCat.{v} R) (φ : A ⟶ B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧
        ∃ x : (M.scalarHom (π ^ n)).kernelPoints B,
          (M.torsionTransition π h).app B x = (M.torsionPointFunctor (π ^ m)).map φ y := by
  obtain ⟨B, φ, hflat, hfp, x, hx⟩ := hM.scalarPower_locallySurjective (n - m) A y.val
  rw [scalarHom_onAlgebraPoints] at hx
  have hy := (M.mem_scalarKernel (π ^ m) A y.val).mp y.property
  have hkill : π ^ n • x = 0 := by
    calc
      π ^ n • x = π ^ m • (π ^ (n - m) • x) := by
        rw [← mul_smul, ← pow_add, Nat.add_comm m (n - m), Nat.sub_add_cancel h]
      _ = M.algebraMapPoints φ.hom (π ^ m • y.val) := by rw [hx, map_smul]
      _ = 0 := by rw [hy, map_zero]
  refine ⟨B, φ, hflat, hfp, ⟨x, (M.mem_scalarKernel (π ^ n) B x).mpr hkill⟩, ?_⟩
  apply Subtype.ext
  exact (torsionTransition_app_val M π h _).trans hx

end Langlands.FormalGroup.ModuleLaw
