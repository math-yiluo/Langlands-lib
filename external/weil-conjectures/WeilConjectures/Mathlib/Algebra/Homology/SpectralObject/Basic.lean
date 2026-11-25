/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ExactSequence

/-!
# Evaluation functors and exact functors on spectral objects

We record the evaluation functors `SpectralObject.hFunctor n D : SpectralObject C ι ⥤ C`,
a criterion for the map `Hⁿ(f) ⟶ Hⁿ(f ≫ g)` to be an isomorphism, and the functor
`Functor.mapSpectralObject` induced on spectral objects by an exact functor.

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian.SpectralObject

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

/-- The functor `Y ↦ Hⁿ(D)` evaluating a spectral object at the degree `n` and the arrow `D`. -/
@[simps]
def hFunctor (n : ℤ) (D : ComposableArrows ι 1) : SpectralObject C ι ⥤ C where
  obj Y := (Y.H n).obj D
  map φ := (φ.hom n).app D

/-- If `hⁿ⁻¹(g)` and `hⁿ(g)` vanish, then the map `hⁿ(f) ⟶ hⁿ(f ≫ g)` is an isomorphism. -/
lemma isIso_H_map_twoδ₂Toδ₁ (X : SpectralObject C ι)
    (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι} (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂)
    (hfg : f ≫ g = fg) (h₀ : IsZero ((X.H n₀).obj (mk₁ g)))
    (h₁ : IsZero ((X.H n₁).obj (mk₁ g))) :
    IsIso ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) := by
  have : Mono ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
    (X.exact₁ f g fg hfg n₀ n₁ hn₁).mono_g (h₀.eq_of_src _ _)
  have : Epi ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
    (X.exact₂ f g fg hfg n₁).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Constructor for isomorphisms of spectral objects: a family of isomorphisms
`X.H n ≅ Y.H n` which commute with the connecting homomorphisms. -/
@[simps]
def isoMk {X Y : SpectralObject C ι} (e : ∀ n : ℤ, X.H n ≅ Y.H n)
    (comm : ∀ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k),
      X.δ f g n₀ n₁ hn₁ ≫ (e n₁).hom.app (mk₁ f) = (e n₀).hom.app (mk₁ g) ≫ Y.δ f g n₀ n₁ hn₁) :
    X ≅ Y where
  hom := { hom n := (e n).hom, comm := comm }
  inv :=
    { hom n := (e n).inv
      comm n₀ n₁ hn₁ i j k f g := by
        rw [← cancel_epi ((e n₀).hom.app (mk₁ g)), ← reassoc_of% (comm n₀ n₁ hn₁ f g)]
        simp }
  hom_inv_id := Hom.ext (funext fun n ↦ (e n).hom_inv_id)
  inv_hom_id := Hom.ext (funext fun n ↦ (e n).inv_hom_id)

variable {C' : Type*} [Category* C'] [Abelian C']

/-- The image of a spectral object under an exact functor `F`: its functors are `H n ⋙ F` and
its connecting homomorphisms are the images under `F` of those of `X`. -/
@[simps]
def mapExact (X : SpectralObject C ι) (F : C ⥤ C') [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : SpectralObject C' ι where
  H n := X.H n ⋙ F
  δ' n₀ n₁ h := Functor.whiskerRight (X.δ' n₀ n₁ h) F
  exact₁' n₀ n₁ h D := (X.exact₁' n₀ n₁ h D).map_mk₂ F
  exact₂' n D := (X.exact₂' n D).map_mk₂ F
  exact₃' n₀ n₁ h D := (X.exact₃' n₀ n₁ h D).map_mk₂ F

end Abelian.SpectralObject

namespace Functor

variable {C C' : Type*} [Category* C] [Abelian C] [Category* C'] [Abelian C']

/-- The functor on spectral objects induced by an exact functor `F : C ⥤ C'`. -/
@[simps]
def mapSpectralObject (F : C ⥤ C') [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (ι : Type*) [Category* ι] :
    Abelian.SpectralObject C ι ⥤ Abelian.SpectralObject C' ι where
  obj X := X.mapExact F
  map {X Y} φ :=
    { hom n := Functor.whiskerRight (φ.hom n) F
      comm n₀ n₁ h _ _ _ f g := by
        change F.map (X.δ f g n₀ n₁ h) ≫ F.map ((φ.hom n₁).app (mk₁ f)) =
          F.map ((φ.hom n₀).app (mk₁ g)) ≫ F.map (Y.δ f g n₀ n₁ h)
        rw [← F.map_comp, ← F.map_comp, φ.comm] }

end Functor

end CategoryTheory
