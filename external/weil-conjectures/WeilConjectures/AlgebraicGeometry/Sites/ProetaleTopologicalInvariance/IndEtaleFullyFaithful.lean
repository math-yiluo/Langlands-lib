/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithfulAlgebra
public import WeilConjectures.RingTheory.ProEtale.IndEtale

/-!
# Base change along a universal homeomorphism is fully faithful on ind-étale algebras

Let `A'` be an `A`-algebra which is a universal homeomorphism. For an ind-étale `A`-algebra
`D₁` and an arbitrary `A`-algebra `D₂`, base change `f ↦ A' ⊗[A] f` is a bijection
`(D₁ →ₐ[A] D₂) ≃ (A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂)`.

The étale case is `Algebra.IsUniversalHomeomorphism.existsUnique_algHom` (a consequence of the
topological invariance of the small étale site, [Stacks 04DZ]). The general case follows by
writing `D₁` as a filtered colimit of étale algebras: maps out of `D₁` are compatible families
of maps out of the stages, and an `A'`-algebra map out of `A' ⊗[A] D₁` is determined by its
values on the elements `1 ⊗ₜ d`.

## Main statements

- `Algebra.IsUniversalHomeomorphism.existsUnique_algHom_of_indEtale`: every `A'`-algebra map
  `A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂` is the base change of a unique `A`-algebra map.
- `Algebra.IsUniversalHomeomorphism.bijective_tensorProductMap`: the same statement in the
  form of bijectivity of base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.IsUniversalHomeomorphism

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  [Algebra.IsUniversalHomeomorphism A A']
  {D₁ D₂ : Type u} [CommRing D₁] [CommRing D₂] [Algebra A D₁] [Algebra A D₂]

omit [Algebra.IsUniversalHomeomorphism A A'] in
/-- Base change of `A`-algebra maps along `A → A'` is compatible with composition. -/
lemma tensorProductMap_comp {E : Type u} [CommRing E] [Algebra A E]
    (f : D₁ →ₐ[A] D₂) (g : E →ₐ[A] D₁) :
    Algebra.TensorProduct.map (AlgHom.id A' A') (f.comp g) =
      (Algebra.TensorProduct.map (AlgHom.id A' A') f).comp
        (Algebra.TensorProduct.map (AlgHom.id A' A') g) := by
  ext x
  simp

/-- **Full faithfulness of base change along a universal homeomorphism on ind-étale
algebras**: if `D₁` is ind-étale over `A`, every `A'`-algebra map
`A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂` is the base change of a unique `A`-algebra map
`D₁ →ₐ[A] D₂`. -/
theorem existsUnique_algHom_of_indEtale [Algebra.IndEtale A D₁]
    (ψ : A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂) :
    ∃! φ : D₁ →ₐ[A] D₂, Algebra.TensorProduct.map (AlgHom.id A' A') φ = ψ := by
  obtain ⟨ι, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D₁)
  have hcolim : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) P.isColimit
  -- The structure maps `ιᵢ: Dᵢ → D₁` of the presentation.
  let s (i : ι) : P.diag.obj i →ₐ[A] D₁ := (P.ι.app i).hom
  have hs {i j : ι} (t : i ⟶ j) : (s j).comp (P.diag.map t).hom = s i := by
    ext x
    exact congr($(P.w t).hom x)
  -- Restricting `ψ` to the étale stages and descending.
  have hex (i : ι) : ∃! φ : P.diag.obj i →ₐ[A] D₂,
      Algebra.TensorProduct.map (AlgHom.id A' A') φ =
        ψ.comp (Algebra.TensorProduct.map (AlgHom.id A' A') (s i)) := haveI := hP i
    existsUnique_algHom (B := A') (ψ.comp (Algebra.TensorProduct.map (AlgHom.id A' A') (s i)))
  choose φ hφ hφu using hex
  beta_reduce at hφ hφu
  have hcompat {i j : ι} (t : i ⟶ j) : (φ j).comp (P.diag.map t).hom = φ i := by
    refine hφu i _ ?_
    rw [tensorProductMap_comp, hφ j, AlgHom.comp_assoc, ← tensorProductMap_comp, hs]
  let c : Cocone P.diag :=
    { pt := CommAlgCat.of A D₂
      ι := { app i := CommAlgCat.ofHom (φ i)
             naturality {i j} t := by
               ext x
               exact congr($(hcompat t) x) } }
  let φ₀ : D₁ →ₐ[A] D₂ := (P.isColimit.desc c).hom
  have hφ₀ (i : ι) : φ₀.comp (s i) = φ i := by
    ext x
    exact congr($(P.isColimit.fac c i).hom x)
  -- Two `A`-algebra maps out of `D₁` agreeing on all stages agree.
  have hext {g₁ g₂ : D₁ →ₐ[A] D₂} (h : ∀ i, g₁.comp (s i) = g₂.comp (s i)) : g₁ = g₂ := by
    ext x
    obtain ⟨i, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcolim x
    exact congr($(h i) y)
  -- Base change of `φ₀` is `ψ`.
  have hmain : Algebra.TensorProduct.map (AlgHom.id A' A') φ₀ = ψ := by
    refine Algebra.TensorProduct.ext' fun a x ↦ ?_
    obtain ⟨i, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcolim x
    have h₁ := congr($(hφ i) (a ⊗ₜ y))
    rw [← hφ₀ i] at h₁
    simpa using h₁
  refine ⟨φ₀, hmain, fun g hg ↦ hext fun i ↦ ?_⟩
  rw [hφ₀ i]
  refine hφu i _ ?_
  rw [tensorProductMap_comp, hg]

/-- **Full faithfulness of base change along a universal homeomorphism on ind-étale
algebras**: if `A'` is a universal homeomorphism over `A` and `D₁` is ind-étale over `A`, then
`f ↦ A' ⊗[A] f` is a bijection `(D₁ →ₐ[A] D₂) → (A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂)` for every
`A`-algebra `D₂` (in particular for ind-étale `D₂`). -/
theorem bijective_tensorProductMap (A A' D₁ D₂ : Type u) [CommRing A] [CommRing A']
    [CommRing D₁] [CommRing D₂] [Algebra A A'] [Algebra A D₁] [Algebra A D₂]
    [Algebra.IsUniversalHomeomorphism A A'] [Algebra.IndEtale A D₁] :
    Function.Bijective (fun f : D₁ →ₐ[A] D₂ ↦
      (Algebra.TensorProduct.map (AlgHom.id A' A') f : A' ⊗[A] D₁ →ₐ[A'] A' ⊗[A] D₂)) := by
  refine ⟨fun f g hfg ↦ ?_, fun ψ ↦ (existsUnique_algHom_of_indEtale ψ).exists⟩
  obtain ⟨φ, -, hφ⟩ := existsUnique_algHom_of_indEtale
    (A' := A') (Algebra.TensorProduct.map (AlgHom.id A' A') g)
  exact (hφ f hfg).trans (hφ g rfl).symm

end Algebra.IsUniversalHomeomorphism
