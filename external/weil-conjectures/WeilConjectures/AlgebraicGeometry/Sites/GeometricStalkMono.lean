/-
Copyright (c) 2026 The Weil conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sheafB
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Geometric stalks detect monomorphisms of abelian étale sheaves

Let `S` be a scheme and `(s i : Spec Ω i ⟶ S)` a family of geometric points of `S` whose
images cover `S`. A morphism `φ : F ⟶ G` of abelian sheaves on the small étale site of `S` is
a monomorphism if and only if all the induced maps of geometric stalks `F_{s i} ⟶ G_{s i}`
are injective.

This is a consequence of Mathlib's
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale` (moved to the coefficient universe by
`Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ`)
and `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **Monomorphisms of étale sheaves are detected on a covering family of geometric stalks.**
Let `(s i: Spec Ω i ⟶ S)` be geometric points of `S` (the `Ω i` algebraically closed) whose
images cover `S`. A morphism `φ: F ⟶ G` of abelian sheaves on the small étale site of `S` is a
monomorphism if and only if every stalk map `φ_{s i}: F_{s i} ⟶ G_{s i}` is injective. -/
theorem mono_iff_forall_injective_sheafFiber_map {S : Scheme.{u}} {ι : Type u}
    {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsAlgClosed (Ω i)]
    (s : ∀ i, Spec (.of (Ω i)) ⟶ S) (hs : ⋃ i, Set.range (s i) = Set.univ)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    Mono φ ↔ ∀ i, Function.Injective ((pointSmallEtale (s i)).sheafFiber.map φ) := by
  refine ⟨fun _ i ↦ ?_, fun h ↦ ?_⟩
  · rw [← AddCommGrpCat.mono_iff_injective]
    have : HasFiniteLimits AddCommGrpCat.{u + 1} := inferInstance
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    have : LocallySmall.{u} S.Etale := inferInstance
    have : PreservesFiniteLimits ((pointSmallEtale (s i)).sheafFiber
      (A := AddCommGrpCat.{u + 1})) := inferInstance
    infer_instance
  · have hP := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ S s hs
    have hmono (Φ : (ObjectProperty.ofObj fun i ↦
        (pointSmallEtale (s i)).ulift.{u + 1}).FullSubcategory) :
        Mono (Φ.obj.sheafFiber.map φ) := by
      obtain ⟨-, ⟨i⟩⟩ := Φ
      have e := GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
        (pointSmallEtale (s i)) AddCommGrpCat.{u + 1}
      have : Mono ((pointSmallEtale (s i)).sheafFiber.map φ) :=
        (AddCommGrpCat.mono_iff_injective _).2 (h i)
      have heq : ((pointSmallEtale (s i)).ulift.{u + 1}).sheafFiber.map φ =
          e.hom.app F ≫ (pointSmallEtale (s i)).sheafFiber.map φ ≫ e.inv.app G := by
        rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
          Category.comp_id]
      exact heq ▸ inferInstance
    exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u + 1}).mono φ

end AlgebraicGeometry.Scheme
