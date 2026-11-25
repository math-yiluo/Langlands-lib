/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldScalarPresheafPullbackExists
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.PresheafPullbackEvaluation
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Exactness of extension from a constant field presheaf

Source: Stacks Project, Modules, Tag 02N4; Sheaves on Spaces, Tag 0095.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

private theorem fieldModuleFunctor_preservesMonomorphisms
    {k : Type u} [Field k] {D : Type*} [Category D]
    (F : ModuleCat.{max u v} k ⥤ D) : F.PreservesMonomorphisms where
  preserves {M N} f _ := by
    obtain ⟨g, hg⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp inferInstance))
    have hfg : f ≫ ModuleCat.ofHom g = 𝟙 M := by
      ext x
      exact LinearMap.congr_fun hg x
    have : IsSplitMono (F.map f) := IsSplitMono.mk'
      { retraction := F.map (ModuleCat.ofHom g)
        id := by rw [← F.map_comp, hfg, F.map_id] }
    infer_instance

/-- Extension from the constant field presheaf preserves monomorphisms before
sheafification.

Source: Stacks Project, Modules, Tag 02N4; Sheaves on Spaces, Tag 0095.
(blueprint: lem-sc-field-scalar-presheaf-pullback-mono).

Proof: put α_U = R(X -> U) ∘ α. The identity-site presheaf pullback is computed
at U by R(U) ⊗[k] V(U). Here R(U) is a right k-module by a · c = a α_U(c),
and left R(U) acts on the first factor by left multiplication. This bimodule
construction does not assume that R(U) is commutative or that α_U(k) is central.
Its universal property gives the natural sectionwise tensor description of the
Mathlib presheaf pullback. A monomorphism of module presheaves is injective at
every open. Every right module over a field is flat, so tensoring these injections
with R(U) remains injective. Hence the image morphism is pointwise injective and
therefore a monomorphism of R-module presheaves. If R(U) is the zero ring, the
tensor is zero and the assertion still holds; the empty space also needs no
nonempty-open assumption. -/
theorem fieldScalarPresheafPullback_preservesMonomorphisms
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    letI := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
    (PresheafOfModules.pullback.{max u v}
      (fieldScalarPresheafRingMap X R α)).PreservesMonomorphisms := by
  let := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
  refine ⟨fun {M N} f _ ↦ ?_⟩
  apply PresheafOfModules.mono_of_injective
  intro U
  obtain ⟨e⟩ := PresheafOfModules.nonempty_pullbackEvaluationIso.{u, v}
    R.obj (fieldScalarPresheafRingMap X R α) U
  have := fieldModuleFunctor_preservesMonomorphisms (k := k)
    (ModuleCat.ringExtendScalars.{u, v} ((fieldScalarPresheafRingMap X R α).app U).hom)
  have := Functor.PreservesMonomorphisms.of_iso e.symm
  apply (ModuleCat.mono_iff_injective
    ((PresheafOfModules.pullback (fieldScalarPresheafRingMap X R α) ⋙
      PresheafOfModules.evaluation R.obj U).map f)).mp
  infer_instance

end SheafOfModules
