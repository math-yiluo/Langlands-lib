/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.RestrictScalars

/-!
# Extensions of bounded constructible complexes killed by an ideal of finite index

Let `Λ` be a noetherian ring and `J` an ideal of `Λ` with `Λ ⧸ J` finite. In a distinguished
triangle `K ⟶ L ⟶ M ⟶ K⟦1⟧` of `D(X_ét, Λ)` with `K` and `M` bounded constructible and `L`
killed by `J`, the middle vertex `L` is bounded constructible
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`): each
homology sheaf of `L` is killed by `J` and is an extension of a kernel by a cokernel of maps
between constructible sheaves, so it is constructible by
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_smul_eq_zero`.

This replaces the closure of constructible sheaves under extensions, which is only available
over a finite coefficient ring, for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` at the integral stage
`Λ = 𝒪_E` of the `ℓ`-adic formalism.
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {A : Type u'} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

/-- **The middle term of a five-term exact sequence lies in a class closed under kernels and
cokernels**, provided it lies in the class whenever it is an extension of two objects of the
class: it is an extension of the kernel of `X₃ ⟶ X₄` by the cokernel of `X₀ ⟶ X₁`. This
variant of `CategoryTheory.ObjectProperty.prop_of_exact_of_exact_of_exact` only asks for the
extension property for the middle term `X₂`. -/
lemma ObjectProperty.prop_of_exact_of_exact_of_exact_of_extension [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels]
    {X₀ X₁ X₂ X₃ X₄ : A} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {w₀ : f₀ ≫ f₁ = 0} {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0}
    (h₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (hX₀ : P X₀) (hX₁ : P X₁) (hX₃ : P X₃) (hX₄ : P X₄)
    (hext : ∀ {Y₁ Y₃ : A} (i : Y₁ ⟶ X₂) (p : X₂ ⟶ Y₃) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact → P Y₁ → P Y₃ → P X₂) : P X₂ := by
  -- the exact sequence `coker f₀ ⟶ X₂ ⟶ X₃`
  let S₁ : ShortComplex A := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ (by
    rw [← cancel_epi (cokernel.π f₀), cokernel.π_desc_assoc, w₁, comp_zero])
  have hS₁ : S₁.Exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := cokernel.π f₀, τ₂ := 𝟙 _, τ₃ := 𝟙 _ } : ShortComplex.mk f₁ f₂ w₁ ⟶ S₁)).mp h₁
  -- the short exact sequence `coker f₀ ⟶ X₂ ⟶ ker f₃`
  let S : ShortComplex A := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) (kernel.lift f₃ f₂ w₂) (by
    rw [← cancel_mono (kernel.ι f₃), Category.assoc, kernel.lift_ι, zero_comp]
    exact S₁.zero)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        ({ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι f₃ } : S ⟶ S₁)).mpr hS₁
      mono_f := h₀.mono_cokernelDesc
      epi_g := h₂.epi_kernelLift }
  exact hext _ _ _ hS (P.prop_cokernel f₀ hX₀ hX₁) (P.prop_kernel f₃ hX₃ hX₄)

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

section ContainsZero

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [PreservesFiniteLimits (CategoryTheory.forget A)] (X : Scheme.{u})

/-- `Dᵇc(X, A)` contains the zero object; unlike
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated` this needs no
closure property of the constructible sheaves. -/
instance Etale.DerivedCategory.containsZero_boundedConstructible :
    (Etale.DerivedCategory.boundedConstructible A X).ContainsZero := by
  rw [Etale.DerivedCategory.boundedConstructible, Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

end ContainsZero

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {J : Ideal Λ}
  [Finite (Λ ⧸ J)]

/-- **Extensions of bounded constructible complexes killed by an ideal of finite index.** For
`Λ` noetherian and `Λ ⧸ J` finite, the middle vertex of a distinguished triangle of
`D(X_ét, Λ)` whose outer vertices are bounded constructible is bounded constructible as soon as
it is killed by `J`: each of its homology sheaves is killed by `J`, the homology functors being
`Λ`-linear, and is an extension of a kernel by a cokernel of maps between constructible sheaves
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_smul_eq_zero`). -/
lemma Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero
    {T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))}
    (hT : T ∈ distTriang _)
    (h₁ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X T.obj₁)
    (h₃ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X T.obj₃)
    (hJ : ∀ r ∈ J, r • 𝟙 T.obj₂ = 0) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X T.obj₂ := by
  refine ⟨_root_.DerivedCategory.TStructure.t.bounded.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
    fun n ↦ ?_⟩
  have hc₁ := h₁.2
  have hc₃ := h₃.2
  have hn : ∀ r ∈ J, r • 𝟙 ((_root_.DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj T.obj₂) = 0 := fun r hr ↦ by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hJ r hr, Functor.map_zero]
  exact ObjectProperty.prop_of_exact_of_exact_of_exact_of_extension
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X)
    ((_root_.DerivedCategory.homologyFunctor _ 0).homologySequence_exact₁ T hT (n - 1) n (by lia))
    ((_root_.DerivedCategory.homologyFunctor _ 0).homologySequence_exact₂ T hT n)
    ((_root_.DerivedCategory.homologyFunctor _ 0).homologySequence_exact₃ T hT n (n + 1) rfl)
    (hc₃ (n - 1)) (hc₁ n) (hc₃ n) (hc₁ (n + 1)) fun i p w hS hY₁ hY₃ ↦
      have : IsConstructibleSheaf (ShortComplex.mk i p w).X₁ := hY₁
      have : IsConstructibleSheaf (ShortComplex.mk i p w).X₃ := hY₃
      IsConstructibleSheaf.of_shortExact_of_smul_eq_zero J hS hn

end AlgebraicGeometry
