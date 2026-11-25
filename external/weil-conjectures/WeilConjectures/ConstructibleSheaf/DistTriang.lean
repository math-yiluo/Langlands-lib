/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite locally constant cohomology sheaves in distinguished triangles

Let `Λ` be a finite ring and `A ⟶ B ⟶ C ⟶ A[1]` a distinguished triangle in the derived category
of étale sheaves of `Λ`-modules on a scheme `X`. If all cohomology sheaves of `A` and `C` are
finite locally constant, so are those of `B`: the long exact cohomology sequence presents
`H^n(B)` as an extension of `ker(H^n(C) ⟶ H^{n+1}(A))` by `coker(H^{n-1}(C) ⟶ H^n(A))`, and finite
locally constant sheaves are stable under kernels, cokernels and extensions
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel`,
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.cokernel`,
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact`).

## Main statements

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.homology_obj₂_of_distTriang`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]

/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of étale sheaves of modules over a finite
ring, if the cohomology sheaves of `A` and `C` are finite locally constant, then so is the
`n`-th cohomology sheaf of `B`. -/
theorem IsFiniteLocallyConstantSheaf.homology_obj₂_of_distTriang
    (T : Triangle (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _)
    (h₁ : ∀ n : ℤ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((DerivedCategory.homologyFunctor _ n).obj T.obj₁))
    (h₃ : ∀ n : ℤ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((DerivedCategory.homologyFunctor _ n).obj T.obj₃))
    (n : ℤ) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((DerivedCategory.homologyFunctor _ n).obj T.obj₂) := by
  have : IsNoetherianRing Λ := inferInstance
  let H := DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let δ₀ := DerivedCategory.HomologySequence.δ T (n - 1) n (by lia)
  let δ₁ := DerivedCategory.HomologySequence.δ T n (n + 1)
  have := h₁ n
  have := h₁ (n + 1)
  have := h₃ (n - 1)
  have := h₃ n
  have := IsFiniteLocallyConstantSheaf.cokernel δ₀
  have := IsFiniteLocallyConstantSheaf.kernel δ₁
  -- `H^{n-1}(C) ⟶ H^n(A) ⟶ H^n(B)`, `H^n(A) ⟶ H^n(B) ⟶ H^n(C)`, `H^n(B) ⟶ H^n(C) ⟶ H^{n+1}(A)`
  have e₁ := DerivedCategory.HomologySequence.exact₁ T hT (n - 1) n (by lia)
  have e₂ := DerivedCategory.HomologySequence.exact₂ T hT n
  have e₃ := DerivedCategory.HomologySequence.exact₃ T hT n (n + 1)
  let f : Limits.cokernel δ₀ ⟶ (H n).obj T.obj₂ := cokernel.desc δ₀ ((H n).map T.mor₁)
    (DerivedCategory.HomologySequence.δ_comp T hT (n - 1) n (by lia))
  let g : (H n).obj T.obj₂ ⟶ Limits.kernel δ₁ := kernel.lift δ₁ ((H n).map T.mor₂)
    (DerivedCategory.HomologySequence.comp_δ T hT n (n + 1))
  have hf : Mono f := e₁.mono_cokernelDesc
  have hg : Epi g := e₃.epi_kernelLift
  let S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ShortComplex.mk f g (by
      rw [← cancel_epi (cokernel.π δ₀), ← cancel_mono (kernel.ι δ₁)]
      simp [f, g, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT])
  -- the middle exactness comes from that of `H^n(A) ⟶ H^n(B) ⟶ H^n(C)`
  let S' : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ShortComplex.mk f ((H n).map T.mor₂) (by
      rw [← cancel_epi (cokernel.π δ₀)]
      simp [f, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT])
  let φ₁ : ShortComplex.mk ((H n).map T.mor₁) ((H n).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]) ⟶
      S' :=
    { τ₁ := cokernel.π δ₀
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  let φ₂ : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι δ₁ }
  have hS' : S'.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1 e₂
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2 hS'
  have hSE : S.ShortExact := { exact := hS, mono_f := hf, epi_g := hg }
  exact IsFiniteLocallyConstantSheaf.of_shortExact (S := S) hSE

variable (X) in
/-- An object of the derived category of étale sheaves of `Λ`-modules on `X` *has finite locally
constant cohomology* if all its cohomology sheaves are finite locally constant. -/
def HasFiniteLocallyConstantHomology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∀ n : ℤ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((DerivedCategory.homologyFunctor _ n).obj K)

namespace HasFiniteLocallyConstantHomology

variable {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

omit [Finite Λ] in
/-- Having finite locally constant cohomology is invariant under isomorphism. -/
lemma of_iso (hK : HasFiniteLocallyConstantHomology X K) (e : K ≅ L) :
    HasFiniteLocallyConstantHomology X L := fun n ↦
  have := hK n
  IsFiniteLocallyConstantSheaf.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)

omit [Finite Λ] in
/-- Having finite locally constant cohomology is invariant under shifts. -/
lemma shift (hK : HasFiniteLocallyConstantHomology X K) (a : ℤ) :
    HasFiniteLocallyConstantHomology X (K⟦a⟧) := fun n ↦
  have := hK (a + n)
  IsFiniteLocallyConstantSheaf.of_iso (F := (DerivedCategory.homologyFunctor _ (a + n)).obj K)
    ((((DerivedCategory.homologyFunctor _ 0).shiftIso a n (a + n) rfl).app K).symm)

/-- In a distinguished triangle, the middle object has finite locally constant cohomology if
the outer ones have. -/
lemma of_distTriang
    (T : Triangle (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) (h₁ : HasFiniteLocallyConstantHomology X T.obj₁)
    (h₃ : HasFiniteLocallyConstantHomology X T.obj₃) :
    HasFiniteLocallyConstantHomology X T.obj₂ :=
  IsFiniteLocallyConstantSheaf.homology_obj₂_of_distTriang T hT h₁ h₃

end HasFiniteLocallyConstantHomology

end AlgebraicGeometry.Scheme
