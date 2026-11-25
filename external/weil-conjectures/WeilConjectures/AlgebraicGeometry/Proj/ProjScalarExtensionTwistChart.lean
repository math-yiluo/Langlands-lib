/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistChartBasic
import WeilConjectures.AlgebraicGeometry.Proj.ProjTwistQuasicoherent
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # The scalar-extension twist map on a single standard chart

## References

* Stacks Project, Tag 01N2, clause (3), proof on standard opens
* Tag 01MY, the map on localized graded modules
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- A morphism with the prescribed pointwise fraction formula is bijective on every
open inside a scalar-extended standard chart, for one fixed integer twist. -/
theorem scalarExtension_twistMap_basicOpen_bijective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n)
    (W : (Proj ℬ).Opens) (hW : W ≤ basicOpen ℬ (ψ f)) :
    Function.Bijective (η.app W) := by
  have _use_hf := hf
  have _use_hn := hn
  have _use_hW := hW
  let I := Σ n : PNat, 𝒜 (n : ℕ)
  have hcover : (⨆ i : I, basicOpen ℬ (ψ (i.2 : A))) = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    have hxcover : x ∈ ⨆ i, ((mapAffineOpenCover ψ hψ).openCover.f i).opensRange := by
      rw [Scheme.OpenCover.iSup_opensRange]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
    change x ∈ (awayι ℬ (ψ i.2.1) (ψ.map_mem i.2.2) i.1.2).opensRange at hi
    rw [opensRange_awayι] at hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i.1, i.2⟩, hi⟩
  have : (twist 𝒜 j).IsQuasicoherent := isQuasicoherent_twist 𝒜 j
  have : (twist ℬ j).IsQuasicoherent := isQuasicoherent_twist ℬ j
  have hIso : IsIso η := by
    apply Hom.isIso_of_bijective_on_affine_open_cover η
      (fun i : I ↦ basicOpen ℬ (ψ (i.2 : A))) hcover
    · intro i
      exact isAffineOpen_basicOpen ℬ (ψ (i.2 : A)) (ψ.map_mem i.2.2) i.1.2
    · intro i
      exact scalarExtension_twistMap_chart_bijective 𝒜 ℬ β ψ hβψ hgraded hψ j η hη
        (i.1 : ℕ) (i.2 : A) i.2.2 i.1.2
  exact ConcreteCategory.bijective_of_isIso (η.app W)

end AlgebraicGeometry.Proj
