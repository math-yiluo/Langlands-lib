/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedInjectiveRestrictionKernel
import WeilConjectures.AlgebraicGeometry.Morphisms.InjectiveModuleTildeFlasque

/-! # Restricting an injective module to the puncture

## References

* Stacks Project, Tag 09T2, Lemma 36.8.1, and Tag 0A6T, Lemma 51.2.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of an injective module to the puncture is surjective, with kernel
its maximal-ideal-power torsion submodule. -/
theorem injective_punctured_restriction_exact
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (M : ModuleCat.{u} R) [Injective M] :
    (tilde.toOpen M W).hom.ker = Ideal.primaryComponent M (IsLocalRing.maximalIdeal R) ∧
      Function.Surjective (tilde.toOpen M W) := by
  refine ⟨injective_punctured_restriction_kernel R W hW M,
    ?_⟩
  let := injective_tilde_isFlasque R M
  let F := (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf
  have hs : Function.Surjective (F.map (homOfLE (show W ≤ ⊤ from le_top)).op) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have ht : Function.Surjective (tilde.toOpen (R := .of R) M ⊤) :=
    by
      change Function.Surjective (tilde.isoTop (R := .of R) M).hom
      exact (ConcreteCategory.bijective_of_isIso _).surjective
  intro s
  obtain ⟨t, ht'⟩ := hs s
  obtain ⟨x, hx⟩ := ht t
  refine ⟨x, ?_⟩
  have he := congrArg (fun f ↦ f x)
    (tilde.toOpen_res (R := .of R) M ⊤ W (homOfLE le_top))
  change F.map (homOfLE (show W ≤ ⊤ from le_top)).op
    (tilde.toOpen (R := .of R) M ⊤ x) = tilde.toOpen M W x at he
  rw [hx, ht'] at he
  exact he.symm

end AlgebraicGeometry.Scheme
