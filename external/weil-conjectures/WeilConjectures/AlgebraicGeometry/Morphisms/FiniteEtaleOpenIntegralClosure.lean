/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenGenericAlgebra

/-!
# Affine integral closures of finite etale covers of normal opens

## References

* Stacks Project, Tag 032L (finite separable integral closure)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The affine algebra defining the relative normalization in a finite etale open cover
is finite over the affine base ring. -/
theorem finiteEtale_open_integralClosure_finite {X : Scheme.{u}} [IsNoetherian X]
    [IsIntegral X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (P : U.toScheme.FiniteEtale) (V : X.Opens)
    (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) :=
      ((P.obj.hom ≫ U.ι).app V).hom.toAlgebra
    Module.Finite Γ(X, V)
      (integralClosure Γ(X, V) Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V)) := by
  classical
  let f := P.obj.hom ≫ U.ι
  let : Algebra Γ(X, V) Γ(P.obj.left, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  cases (V : Set X).eq_empty_or_nonempty with
  | inl h =>
    have hV0 : V = ⊥ := SetLike.ext' h
    subst V
    have : Subsingleton Γ(P.obj.left, f ⁻¹ᵁ (⊥ : X.Opens)) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    exact Module.Finite.of_finite
  | inr h =>
    have : Nonempty V := by simpa using h
    let A : Type u := Γ(X, V)
    let B : Type u := Γ(P.obj.left, f ⁻¹ᵁ V)
    let K := FractionRing A
    have : IsDomain A := IsIntegral.component_integral V
    have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsIntegrallyClosed A := by
      apply IsIntegrallyClosed.of_localization_maximal
      intro p hp hpmax
      let y : PrimeSpectrum A := ⟨p, inferInstance⟩
      have hy : hV.fromSpec y ∈ V := by
        rw [← SetLike.mem_coe, ← hV.range_fromSpec]
        exact Set.mem_range_self y
      let := X.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
      have := hV.isLocalization_stalk' y hy
      have := hX (hV.fromSpec y)
      exact IsIntegrallyClosed.of_equiv
        (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hV.fromSpec y))
          (Localization.AtPrime p)).toRingEquiv
    obtain ⟨D, hD, aD, hfin, het, e, he⟩ :=
      exists_finiteEtale_open_generic_algebra U P V hV
    let := hD
    let := aD
    let : Module.Finite K D := hfin
    let : Algebra.FormallyEtale K D := het
    let : Algebra A D := Algebra.compHom D (algebraMap A K)
    have : IsScalarTower A K D := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : _root_.IsReduced D := Algebra.FormallyUnramified.isReduced_of_field K D
    have : IsArtinianRing D := IsArtinianRing.of_finite K D
    let L (m : MaximalSpectrum D) := D ⧸ m.asIdeal
    let : ∀ m : MaximalSpectrum D, Field (L m) := fun m => Ideal.Quotient.field m.asIdeal
    have : ∀ m : MaximalSpectrum D, Module.Finite K (L m) := fun m => inferInstance
    have : ∀ m : MaximalSpectrum D, Algebra.IsSeparable K (L m) :=
      fun m => inferInstance
    let : ∀ m : MaximalSpectrum D, Algebra A (L m) :=
      fun m => Algebra.compHom (L m) (algebraMap A K)
    have : ∀ m : MaximalSpectrum D, IsScalarTower A K (L m) :=
      fun m => IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : ∀ m : MaximalSpectrum D, Module.Finite A (integralClosure A (L m)) :=
      fun m => IsIntegralClosure.finite A K (L m) (integralClosure A (L m))
    let ed := (IsArtinianRing.equivPi D).restrictScalars A
    let em (m : MaximalSpectrum D) : B →ₐ[A] L m :=
      (Pi.evalAlgHom A (fun m => L m) m).comp (ed.toAlgHom.comp e)
    let F : (integralClosure A B) →ₗ[A] ∀ m : MaximalSpectrum D,
        integralClosure A (L m) :=
      { toFun := fun x m => ⟨em m x, x.property.map (em m)⟩
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }
    apply Module.Finite.of_injective F
    intro x y hxy
    apply Subtype.ext
    apply he
    apply ed.injective
    funext m
    exact congrArg Subtype.val (congrFun hxy m)

end AlgebraicGeometry.Scheme
