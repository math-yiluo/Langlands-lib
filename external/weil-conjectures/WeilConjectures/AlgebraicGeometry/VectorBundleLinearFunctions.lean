/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundle

/-!
# Fibrewise linear functions on a vector bundle chart

The coordinates of `𝔸^n_S` are linearly independent over `Γ(S, ⊤)` (acting through the
projection): evaluating a relation `∑ gⱼ Tⱼ = 0` at the section `T = eᵢ` gives `gᵢ = 0`
(`AlgebraicGeometry.AffineSpace.linearIndependent_coord`). Hence the fibrewise linear functions on
`𝔸^n_S`, the `Γ(S, ⊤)`-span of the coordinates, form a free module with basis the coordinates
(`AlgebraicGeometry.AffineSpace.linearFunctionsBasis`). For a vector bundle given by a linear atlas
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas`), this is the local freeness of rank `c` of the
sheaf `ℰ` of fibrewise linear functions on each chart, the first step of the identification
`E ≅ Spec_Z (Sym^• ℰ)` of `proposition-purity-vector-bundles`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- `Γ(𝔸^n_S, ⊤)` as an algebra over `Γ(S, ⊤)` through the projection. -/
noncomputable abbrev topAlgebra : Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
  (𝔸(n; S) ↘ S).appTop.hom.toAlgebra

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The coordinates of `𝔸^n_S` are linearly independent over `Γ(S, ⊤)`. -/
theorem linearIndependent_coord :
    letI := topAlgebra n S
    LinearIndependent Γ(S, ⊤) (coord S : n → Γ(𝔸(n; S), ⊤)) := by
  classical
  let := topAlgebra n S
  rw [linearIndependent_iff']
  intro s g hg i hi
  let σ : S ⟶ 𝔸(n; S) := homOfVector (𝟙 S) (Pi.single i (1 : Γ(S, ⊤)))
  have hσ (a : Γ(S, ⊤)) : σ.appTop ((𝔸(n; S) ↘ S).appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]
    rfl
  have h := congrArg σ.appTop hg
  rw [map_sum, map_zero] at h
  have hterm (j : n) : σ.appTop (g j • coord S j) =
      g j * (Pi.single i (1 : Γ(S, ⊤)) : n → Γ(S, ⊤)) j := by
    rw [Algebra.smul_def, map_mul]
    change σ.appTop ((𝔸(n; S) ↘ S).appTop (g j)) * _ = _
    rw [hσ, homOfVector_appTop_coord]
  simp only [hterm] at h
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h' ↦ absurd hi h'), Pi.single_eq_same, mul_one] at h
  exact h

/-- The fibrewise linear functions on `𝔸^n_S`: the `Γ(S, ⊤)`-span of the coordinates. -/
noncomputable def linearFunctions :
    letI := topAlgebra n S
    Submodule Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
  letI := topAlgebra n S
  Submodule.span Γ(S, ⊤) (Set.range (coord S))

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The fibrewise linear functions on `𝔸^n_S` form a free `Γ(S, ⊤)`-module with basis the
coordinates. -/
noncomputable def linearFunctionsBasis :
    letI := topAlgebra n S
    Module.Basis n Γ(S, ⊤) (linearFunctions n S) :=
  letI := topAlgebra n S
  Module.Basis.span (linearIndependent_coord n S)

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas

variable {E Z : Scheme.{u}} {c : ℕ} {p : E ⟶ Z} {z : Z ⟶ E}

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The coordinates of a chart `E ×_Z Vᵢ ≅ 𝔸^c_{Vᵢ}` of a linear atlas are linearly independent over
`Γ(Vᵢ, ⊤)` (acting through the projection): the fibrewise linear functions on `E ×_Z Vᵢ` form a
free module of rank `c`. -/
theorem linearIndependent_chart_coord (A : VectorBundleAtlas c p z) (i : A.ι) :
    letI := (pullback.snd p (A.v i)).appTop.hom.toAlgebra
    LinearIndependent Γ(A.V i, ⊤)
      (fun l : ULift.{u} (Fin c) ↦ (A.chart i).hom.appTop (AffineSpace.coord (A.V i) l)) := by
  let := (pullback.snd p (A.v i)).appTop.hom.toAlgebra
  let := AffineSpace.topAlgebra (ULift.{u} (Fin c)) (A.V i)
  have hover : ∀ a, (A.chart i).hom.appTop
      ((𝔸(ULift.{u} (Fin c); A.V i) ↘ A.V i).appTop a) = (pullback.snd p (A.v i)).appTop a := by
    intro a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, A.chart_hom_over]
  let φ : Γ(𝔸(ULift.{u} (Fin c); A.V i), ⊤) →ₗ[Γ(A.V i, ⊤)] Γ(pullback p (A.v i), ⊤) :=
    { toFun := (A.chart i).hom.appTop
      map_add' := map_add _
      map_smul' := fun a x ↦ by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        exact congrArg (· * _) (hover a) }
  have hinj : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso ((A.chart i).hom.appTop)).1
  exact (AffineSpace.linearIndependent_coord _ _).map' φ (LinearMap.ker_eq_bot.2 hinj)

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The fibrewise linear functions on the chart `E ×_Z Vᵢ`: the `Γ(Vᵢ, ⊤)`-span of the chart
coordinates, a free module of rank `c` with basis the coordinates. -/
noncomputable def chartLinearFunctionsBasis (A : VectorBundleAtlas c p z) (i : A.ι) :
    letI := (pullback.snd p (A.v i)).appTop.hom.toAlgebra
    Module.Basis (ULift.{u} (Fin c)) Γ(A.V i, ⊤)
      (Submodule.span Γ(A.V i, ⊤) (Set.range fun l : ULift.{u} (Fin c) ↦
        (A.chart i).hom.appTop (AffineSpace.coord (A.V i) l))) :=
  letI := (pullback.snd p (A.v i)).appTop.hom.toAlgebra
  Module.Basis.span (A.linearIndependent_chart_coord i)

end AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas
