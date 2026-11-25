/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coextension of scalars along a Frobenius extension

Let `R ⟶ S` be a morphism of commutative rings making `S` a finite free `R`-module, and let
`φ : S → R` be a *Frobenius form*: an `R`-linear form such that every `R`-linear form on `S` is
`φ(s * -)` for a unique `s ∈ S`. Then coextension of scalars `M ↦ Hom_R(S, M)` is left adjoint
to restriction of scalars (`ModuleCat.coextendRestrictScalarsAdj`), besides being right adjoint
to it. So coextension of scalars is the extension of scalars `S ⊗_R -`.

## Construction

Let `(bᵢ)` be a basis of `S` over `R` and `(b'ᵢ)` the dual basis for `φ`, characterised by
`φ(b'ᵢ * x) = bᵢ^*(x)`. The unit `M ⟶ Hom_R(S, M)` sends `m` to `s ↦ φ(s) • m`, and the counit
`Hom_R(S, N) ⟶ N` sends `h` to `∑ᵢ b'ᵢ • h(bᵢ)`. Both triangle identities follow from
`∑ᵢ φ(bᵢ * x) • b'ᵢ = x` (`ModuleCat.CoextendScalars.sum_smul_frobeniusDual`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι R S) (φ : S →ₗ[R] R)
  (hφ : Function.Bijective fun s : S ↦ φ ∘ₗ LinearMap.mulLeft R s)

namespace CoextendScalars

/-- The dual basis of `b` with respect to a Frobenius form `φ`: `φ (b' i * x)` is the `i`-th
coordinate of `x` in the basis `b`. -/
noncomputable def frobeniusDual (i : ι) : S :=
  (Equiv.ofBijective _ hφ).symm (b.coord i)

omit [Fintype ι] in
lemma apply_frobeniusDual_mul (i : ι) (x : S) :
    φ (frobeniusDual b φ hφ i * x) = b.coord i x :=
  LinearMap.congr_fun ((Equiv.ofBijective _ hφ).apply_symm_apply (b.coord i)) x

/-- Every `x ∈ S` is `∑ᵢ φ(bᵢ * x) • b'ᵢ`. -/
lemma sum_smul_frobeniusDual (x : S) : ∑ i, φ (b i * x) • frobeniusDual b φ hφ i = x := by
  refine hφ.1 (LinearMap.ext fun y ↦ ?_)
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Finset.sum_mul, map_sum,
    smul_mul_assoc, map_smul, apply_frobeniusDual_mul, smul_eq_mul]
  conv_rhs => rw [← b.sum_repr y]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm x, mul_comm]; rfl

lemma sum_coord_smul_frobeniusDual (t : S) (j : ι) :
    ∑ i, b.coord j (b i * t) • frobeniusDual b φ hφ i = t * frobeniusDual b φ hφ j := by
  conv_rhs => rw [← sum_smul_frobeniusDual b φ hφ (t * frobeniusDual b φ hφ j)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← apply_frobeniusDual_mul b φ hφ j]
  ring_nf

variable (R S) in
/-- `S`, with the `R`-module structure given by restriction of scalars, is `S` as an
`R`-algebra. -/
noncomputable def restrictScalarsSelfLinearEquiv :
    (restrictScalars (algebraMap R S)).obj (of S S) ≃ₗ[R] S where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' r s := (Algebra.smul_def r (show S from s)).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- An `R`-linear map from `S` to the restriction of scalars of `N` is determined by the images
of the basis `b`. -/
lemma apply_eq_sum_smul {N : ModuleCat.{u} S}
    (g : S →ₗ[R] (restrictScalars (algebraMap R S)).obj N) (x : S) :
    (g x : N) = ∑ j, algebraMap R S (b.coord j x) • (g (b j) : N) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ g.map_smul _ _

/-- The element `s ↦ φ(s) • m` of `Hom_R(S, M)`. -/
noncomputable def frobeniusUnitElt {M : ModuleCat.{u} R} (m : M) :
    (coextendScalars (algebraMap R S)).obj M :=
  (CoextendScalars.equiv _ M).symm
    (LinearMap.smulRight φ m ∘ₗ (restrictScalarsSelfLinearEquiv R S).toLinearMap)

lemma frobeniusUnitElt_apply {M : ModuleCat.{u} R} (m : M) (s : S) :
    frobeniusUnitElt φ m s = φ s • m :=
  rfl

/-- The unit `M ⟶ Hom_R(S, M)`, `m ↦ (s ↦ φ(s) • m)`, of the adjunction between coextension
and restriction of scalars along a Frobenius extension. -/
noncomputable def frobeniusUnitApp (M : ModuleCat.{u} R) :
    M ⟶ (restrictScalars (algebraMap R S)).obj ((coextendScalars (algebraMap R S)).obj M) :=
  ofHom (Y := (restrictScalars (algebraMap R S)).obj ((coextendScalars (algebraMap R S)).obj M))
  { toFun m := frobeniusUnitElt φ m
    map_add' m m' := CoextendScalars.ext (LinearMap.ext fun s ↦ smul_add (φ s) m m')
    map_smul' r m := CoextendScalars.ext (LinearMap.ext fun s ↦ by
      change φ s • r • m = φ ((show S from s) * algebraMap R S r) • m
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_smul]
      exact smul_comm _ _ _) }

/-- The counit `Hom_R(S, N) ⟶ N`, `h ↦ ∑ᵢ b'ᵢ • h(bᵢ)`, of the adjunction between coextension
and restriction of scalars along a Frobenius extension. -/
noncomputable def frobeniusCounitApp (N : ModuleCat.{u} S) :
    (coextendScalars (algebraMap R S)).obj ((restrictScalars (algebraMap R S)).obj N) ⟶ N :=
  ofHom
  { toFun h := ∑ i, frobeniusDual b φ hφ i • (h (b i) : N)
    map_add' h h' :=
      (Finset.sum_congr rfl fun i _ ↦ smul_add _ _ _).trans Finset.sum_add_distrib
    map_smul' t h := by
      let g := CoextendScalars.equiv _ _ h ∘ₗ
        (restrictScalarsSelfLinearEquiv R S).symm.toLinearMap
      change ∑ i, frobeniusDual b φ hφ i • (g (b i * t) : N) =
        t • ∑ i, frobeniusDual b φ hφ i • (g (b i) : N)
      simp only [apply_eq_sum_smul b g (_ * t), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_smul, ← sum_coord_smul_frobeniusDual b φ hφ t j]
      simp only [Algebra.smul_def, mul_comm] }

lemma sum_apply_frobeniusDual_mul_smul (s : S) :
    ∑ i, φ (frobeniusDual b φ hφ i * s) • b i = s := by
  simp only [apply_frobeniusDual_mul, Module.Basis.coord_apply]
  exact b.sum_repr s

end CoextendScalars

open CoextendScalars

/-- Along a finite free extension `R ⟶ S` with a Frobenius form `φ` and a basis `b`,
coextension of scalars is left adjoint to restriction of scalars, with unit
`m ↦ (s ↦ φ(s) • m)` and counit `h ↦ ∑ᵢ b'ᵢ • h(bᵢ)`, `(b'ᵢ)` being the dual basis of `b`
for `φ`. -/
noncomputable def coextendRestrictScalarsAdj :
    coextendScalars.{u} (algebraMap R S) ⊣ restrictScalars.{u} (algebraMap R S) where
  unit :=
    { app := frobeniusUnitApp φ
      naturality M M' g := by
        ext m : 2
        refine CoextendScalars.ext (LinearMap.ext fun s ↦ ?_)
        exact (g.hom.map_smul (φ s) m).symm }
  counit :=
    { app := frobeniusCounitApp b φ hφ
      naturality N N' g := by
        ext h : 2
        let h' : (coextendScalars (algebraMap R S)).obj
          ((restrictScalars (algebraMap R S)).obj N) := h
        change ∑ i, frobeniusDual b φ hφ i • g (h' (b i)) =
          g (∑ i, frobeniusDual b φ hφ i • h' (b i))
        exact ((map_sum g.hom _ _).trans
          (Finset.sum_congr rfl fun i _ ↦ g.hom.map_smul _ _)).symm }
  left_triangle_components M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun h ↦ ?_)
    refine CoextendScalars.ext (LinearMap.ext fun (s : S) ↦ ?_)
    let g := CoextendScalars.equiv _ M h ∘ₗ
      (restrictScalarsSelfLinearEquiv R S).symm.toLinearMap
    change CoextendScalars.equiv _ M
      (∑ i, frobeniusDual b φ hφ i • frobeniusUnitElt φ (g (b i))) s = g s
    rw [map_sum]
    refine (LinearMap.sum_apply _ _ _).trans ?_
    change ∑ i, φ (s * frobeniusDual b φ hφ i) • g (b i) = g s
    conv_rhs => rw [← sum_apply_frobeniusDual_mul_smul b φ hφ s]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, mul_comm]
  right_triangle_components N := by
    refine ModuleCat.hom_ext (LinearMap.ext fun n ↦ ?_)
    change ∑ i, frobeniusDual b φ hφ i • (algebraMap R S (φ (b i)) • (n : N)) = n
    simp only [smul_smul, ← Finset.sum_smul]
    conv_rhs => rw [← one_smul S (n : N), ← sum_smul_frobeniusDual b φ hφ 1]
    simp only [one_mul, Algebra.smul_def, mul_comm]

end ModuleCat
