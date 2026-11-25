/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.GradedChainMapsExact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.GradedModuleChartData

/-!
# Exactness of an associated graded chain on the projective line

## References

* Stacks Project, Constructions, Tag 01M7, final paragraph
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Sheafification and inverse transport of a given exact graded chain. The terms need not
be free or finitely generated; the conclusion supplies their associated sheaf chart data. -/
theorem sheafify_graded_chain (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (A : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝒢 : ∀ i : Fin 3, ℤ → AddSubgroup (A i))
    (f₂ : A 2 →ₗ[MvPolynomial (Fin 2) k] A 1)
    (f₁ : A 1 →ₗ[MvPolynomial (Fin 2) k] A 0)
    (f₀ : A 0 →ₗ[MvPolynomial (Fin 2) k] M)
    (h𝒢 : ∀ i : Fin 3, DirectSum.IsInternal (𝒢 i))
    (hA_smul : ∀ (i : Fin 3) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : A i),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j))
    (hf₂ : ∀ (j : ℤ) (x : A 2), x ∈ 𝒢 2 j → f₂ x ∈ 𝒢 1 j)
    (hf₁ : ∀ (j : ℤ) (x : A 1), x ∈ 𝒢 1 j → f₁ x ∈ 𝒢 0 j)
    (hf₀ : ∀ (j : ℤ) (x : A 0), x ∈ 𝒢 0 j → f₀ x ∈ 𝓜 j)
    (hinj : Function.Injective f₂) (hex₁ : LinearMap.range f₂ = LinearMap.ker f₁)
    (hex₀ : LinearMap.range f₁ = LinearMap.ker f₀) (hsurj : Function.Surjective f₀) :
    ∃ (E : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
      (g₂ : (Scheme.Modules.pullback C.iso.inv).obj (E 2) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj (E 1))
      (g₁ : (Scheme.Modules.pullback C.iso.inv).obj (E 1) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj (E 0))
      (g₀ : (Scheme.Modules.pullback C.iso.inv).obj (E 0) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj F),
      (∀ i : Fin 3,
        ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
          0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
          (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
            LocalizedModule.Away f (A i)),
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
            Function.Injective (alpha f d hd hf) ∧
            Set.range (alpha f d hd hf) = degreeZeroFractions
              (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
              (fun n : ℕ ↦ (𝒢 i n : Set (A i))) (Submonoid.powers f)) ∧
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
            alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
              algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
                (Localization.Away f) r • alpha f d hd hf s) ∧
          (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
            (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
              basicOpen (homogeneousSubmodule (Fin 2) k) f)
            (e c : ℕ) (a : MvPolynomial (Fin 2) k),
            0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
            ∀ (m : ℕ) (y : A i)
              (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
              alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
              alpha g b hb hg ((E i).val.map (homOfLE inc).op s) =
                mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))) ∧
      Mono g₂ ∧ Epi g₀ ∧ (ComposableArrows.mk₃ g₂ g₁ g₀).Exact := by
  classical
  have hcharts := fun i : Fin 3 ↦
    graded_module_chart_data_exists k (A i) (𝒢 i) (h𝒢 i) (hA_smul i)
  choose E hE using hcharts
  obtain ⟨g₂, g₁, g₀, hg₂, hg₀, hex⟩ := graded_chain_maps_exact k M 𝓜 h𝓜 hsmul
    F alpha halpha hscalar hres A 𝒢 f₂ f₁ f₀ h𝒢 hA_smul hf₂ hf₁ hf₀ hinj hex₁ hex₀
    hsurj E hE
  let P := Scheme.Modules.pullback C.iso.inv
  let Q := Scheme.Modules.pullback C.iso.hom
  let e : (Proj (homogeneousSubmodule (Fin 2) k)).Modules ≌
      (ProjectiveLine (Spec (.of k))).Modules :=
    CategoryTheory.Equivalence.mk P Q
      ((Scheme.Modules.pullbackComp C.iso.hom C.iso.inv) ≪≫
        Scheme.Modules.pullbackCongr C.iso.hom_inv_id ≪≫
        Scheme.Modules.pullbackId _).symm
      ((Scheme.Modules.pullbackComp C.iso.inv C.iso.hom) ≪≫
        Scheme.Modules.pullbackCongr C.iso.inv_hom_id ≪≫
        Scheme.Modules.pullbackId _)
  have : P.IsEquivalence := e.isEquivalence_functor
  have : Mono g₂ := hg₂
  have : Epi g₀ := hg₀
  refine ⟨E, P.map g₂, P.map g₁, P.map g₀, hE, inferInstance, inferInstance, ?_⟩
  have h₂₁ : g₂ ≫ g₁ = 0 := hex.toIsComplex.zero 0
  have h₁₀ : g₁ ≫ g₀ = 0 := hex.toIsComplex.zero 1
  have hx₂₁ : (ShortComplex.mk g₂ g₁ h₂₁).Exact := hex.exact 0
  have hx₁₀ : (ShortComplex.mk g₁ g₀ h₁₀).Exact := hex.exact 1
  exact ComposableArrows.exact_of_δ₀
    ((hx₂₁.map P).exact_toComposableArrows) ((hx₁₀.map P).exact_toComposableArrows)

end AlgebraicGeometry.Proj
