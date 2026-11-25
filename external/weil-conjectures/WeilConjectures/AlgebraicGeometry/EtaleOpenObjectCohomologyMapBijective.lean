/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectHomBijective
import Mathlib.Algebra.FiveLemma
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Bijectivity of the canonical open-object cohomology map

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private lemma extComparison_bijective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [EnoughInjectives C]
    (R : C ⥤ D) [R.Additive] [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
    [R.PreservesInjectiveObjects] (A : C) (Z : D) (k : Z ⟶ R.obj A)
    (hzero : ∀ F : C, Function.Bijective (fun f : A ⟶ F ↦ k ≫ R.map f))
    (F : C) (q : ℕ) :
    Function.Bijective
      (((Abelian.Ext.mk₀ k).precomp _ (zero_add q)).comp (R.mapExtAddHom A F q)) := by
  classical
  let m (G : C) (n : ℕ) : Abelian.Ext A G n →+ Abelian.Ext Z (R.obj G) n :=
    ((Abelian.Ext.mk₀ k).precomp _ (zero_add n)).comp (R.mapExtAddHom A G n)
  change Function.Bijective (m F q)
  induction q generalizing F with
  | zero =>
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
      change (Abelian.Ext.mk₀ k).comp
        ((Abelian.Ext.mk₀ x).mapExactFunctor R) rfl =
          (Abelian.Ext.mk₀ k).comp ((Abelian.Ext.mk₀ y).mapExactFunctor R) rfl at hxy
      rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_mk₀,
        Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀] at hxy
      exact congrArg Abelian.Ext.mk₀ ((hzero F).1
        ((Abelian.Ext.mk₀_bijective _ _).1 hxy))
    · obtain ⟨z, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 z
      obtain ⟨f, hf⟩ := (hzero F).2 z
      refine ⟨Abelian.Ext.mk₀ f, ?_⟩
      change (Abelian.Ext.mk₀ k).comp ((Abelian.Ext.mk₀ f).mapExactFunctor R) rfl = _
      rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
      exact congrArg Abelian.Ext.mk₀ hf
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    have := I.injective
    have : Injective (R.obj I.J) := Functor.injective_obj R I.J
    let S := ShortComplex.mk I.f (Limits.cokernel.π I.f) (Limits.cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hT : (S.map R).ShortExact := hS.map_of_exact R
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ S.g).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
      ((Abelian.Ext.mk₀ (R.map S.g)).postcomp Z (add_zero n))
      (hT.extClass.postcomp Z rfl)
      (m S.X₂ n) (m S.X₃ n) (m S.X₁ (n + 1))
      (by
        apply AddMonoidHom.ext
        intro x
        change ((Abelian.Ext.mk₀ k).comp (x.mapExactFunctor R) (zero_add n)).comp
            (Abelian.Ext.mk₀ (R.map S.g)) (add_zero n) =
          (Abelian.Ext.mk₀ k).comp
            ((x.comp (Abelian.Ext.mk₀ S.g) (add_zero n)).mapExactFunctor R) (zero_add n)
        have hm := Abelian.Ext.mapExactFunctor_comp R x (Abelian.Ext.mk₀ S.g) (add_zero n)
        have hg := Abelian.Ext.mapExactFunctor_mk₀ R S.g
        exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ k) (x.mapExactFunctor R)
          (Abelian.Ext.mk₀ (R.map S.g)) (zero_add n) (add_zero n)
          (by omega)).trans
            (congrArg (fun z ↦ (Abelian.Ext.mk₀ k).comp z (zero_add n))
              (hm.trans (congrArg (fun z ↦ (x.mapExactFunctor R).comp z (add_zero n))
                hg)).symm))
      (by
        apply AddMonoidHom.ext
        intro x
        change ((Abelian.Ext.mk₀ k).comp (x.mapExactFunctor R) (zero_add n)).comp
            hT.extClass rfl =
          (Abelian.Ext.mk₀ k).comp
            ((x.comp hS.extClass rfl).mapExactFunctor R) (zero_add (n + 1))
        have hm := Abelian.Ext.mapExactFunctor_comp R x hS.extClass rfl
        have hg := Abelian.Ext.mapExactFunctor_extClass R hS
        exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ k) (x.mapExactFunctor R)
          hT.extClass (zero_add n) rfl (by omega)).trans
          (congrArg (fun z ↦ (Abelian.Ext.mk₀ k).comp z (zero_add (n + 1)))
            (hm.trans (congrArg (fun z ↦ (x.mapExactFunctor R).comp z rfl) hg)).symm))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' Z hT n (n + 1) rfl))
      (hn I.J).2 (hn S.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS x
        (Abelian.Ext.eq_zero_of_injective (I := I.J) _) rfl)
      (fun y ↦ Abelian.Ext.covariant_sequence_exact₁ _ hT y
        (Abelian.Ext.eq_zero_of_injective (I := R.obj I.J) _) rfl)

/-- The canonical identity-generator map is bijective on object cohomology.
Source: Stacks Project, Cohomology on Sites, Tag 03F3, proof of cohomology-of-open.
(blueprint: lem-weil-pbc-etale-open-object-cohomology-map-bijective)

Proof: Choose an injective resolution I of F. Extension by zero along the open is
exact and left adjoint to localization restriction, so restriction preserves injectives.
The inverse-image/restriction comparison identifies the pulled-back resolution with
that restricted resolution. The sheafification, free abelian group and Yoneda
adjunctions identify Hom from the free sheaf at U to I in each degree with I(U).
The constant-sheaf adjunction at the terminal object of U identifies Hom from the
constant integers to the restricted resolution with the same group I(U).
These are additive identifications commuting with the differentials. Their composite
is pullback followed by precomposition with etaleOpenFreeSheafUnit U: the chosen
identity generator is sent to the original section by the Yoneda adjunction.
The Ext/injective-resolution comparison identifies this map on cohomology classes
with etaleOpenObjectCohomologyMap. Hence that map is bijective in every degree.
The argument also applies to degree zero and to the empty open: it compares the
same section complexes, including the zero complex over the empty open. -/
theorem etaleOpenObjectCohomologyMap_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : X.Opens) :
    Function.Bijective (etaleOpenObjectCohomologyMap F q U) := by
  let R := Etale.upperStar AddCommGrpCat.{u + 1} U.ι
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} U.ι)
  exact extComparison_bijective R _ _ (etaleOpenFreeSheafUnit U)
    (fun G ↦ etaleOpenObjectHom_bijective G U) F q

end AlgebraicGeometry
