/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapInjective
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapSurjective

/-! # Invertibility of the fixed raw scalar comparison

Source: Stacks Project, Tag 03FD.
(blueprint: lem-sbc-raw-module-abelian-hom-map-is-iso).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Forgetting the raw class induces an additive bijection.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: lem-sbc-raw-module-abelian-hom-map-is-iso).

Proof: Put V = U times_S A.left. Pullback of the represented free sheaf
corepresents sections on V, for both coefficient categories. Resolve A.hom^*G
by injective module sheaves. Restriction to the etale object V preserves
injectives, since its extension-by-zero left adjoint is exact. After forgetting
scalars this resolution is acyclic for abelian sections by Tag 03FD. Thus both
raw derived Hom groups are cohomology of the same complex of sections. On that
complex the displayed map is the identity: freeMap sends the identity generator
to the identity generator, derived forgetting is termwise forgetting, and the
single, shift and coefficient comparisons identify precisely the same section.
It is consequently bijective and additive, so is an isomorphism in AddCommGrpCat.
This includes degree zero, where it is the sections adjunction, the zero ring,
and empty V, where the section complex is zero. -/
theorem isIso_rawModuleAbelianHomMap
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    IsIso (rawModuleAbelianHomMap Λ k G q U A) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨rawModuleAbelianHomMap_injective Λ k G q U A,
    rawModuleAbelianHomMap_surjective Λ k G q U A⟩

end AlgebraicGeometry.Etale
