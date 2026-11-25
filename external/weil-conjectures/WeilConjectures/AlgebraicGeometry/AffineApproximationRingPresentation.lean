/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.FiniteType

/-! # Ring presentation of affine approximation stages

Source: Stacks Project, Tags 0GS2 and 0A0P.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Express an affine-base proper approximation as a diagram of rings.

Source: Stacks Project, Tag 0A0P, affine-base clause, and Tag 0GS2, General case.
(blueprint: lem-weil-pbc-affine-approximation-ring-presentation).

Proof: Set B to the global-section diagram of Ss, with arrows reversed. Every affine
stage has its canonical isomorphism to Spec of its global sections. Compose fs with
these isomorphisms to obtain g; their naturality makes g a natural transformation.
Compose the global-section cocone of piS with the inverse of the canonical
A-to-global-sections isomorphism of Spec A to obtain alpha. Transporting the given
colimit across this isomorphism gives the required colimit at A. Naturality of the
canonical affine isomorphisms and the given commuting squares give the displayed
squares for p, g, and alpha. Properness is preserved by the isomorphisms; finite type
over the integers is exactly the given finite-type ring-map property. No ideal is
involved in this change of presentation. -/
theorem affine_approximation_ring_presentation
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    {Λ : Type u} [Preorder Λ]
    (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
    (p : (Functor.const Λᵒᵖ).obj Y ⟶ Xs)
    (s : (Functor.const Λᵒᵖ).obj (Spec (.of A)) ⟶ Ss)
    (ha : ∀ i, IsAffine (Ss.obj i))
    (hft : ∀ i, RingHom.FiniteType
      (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i)))))
    (hc : Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk _ s).op)))
    (hp : ∀ i, IsProper (fs.app i))
    (hw : ∀ i, p.app i ≫ fs.app i = f ≫ s.app i) :
    ∃ (B : Λ ⥤ CommRingCat.{u}) (g : Xs ⟶ B.op ⋙ Scheme.Spec)
      (α : B ⟶ (Functor.const Λ).obj (.of A)),
      Nonempty (IsColimit (Cocone.mk _ α)) ∧
      (∀ i, Algebra.FiniteType ℤ (B.obj i)) ∧
      (∀ i, IsProper (g.app i)) ∧
      (∀ i, p.app i ≫ g.app i = f ≫ Spec.map (α.app i.unop)) := by
  let (i : Λᵒᵖ) : IsAffine (Ss.obj i) := ha i
  let B : Λ ⥤ CommRingCat.{u} := Ss.rightOp ⋙ Scheme.Γ
  let g : Xs ⟶ B.op ⋙ Scheme.Spec :=
    { app := fun i ↦ fs.app i ≫ (Ss.obj i).isoSpec.hom
      naturality := by
        intro i j a
        change Xs.map a ≫ (fs.app j ≫ (Ss.obj j).isoSpec.hom) =
          (fs.app i ≫ (Ss.obj i).isoSpec.hom) ≫ Spec.map (Ss.map a).appTop
        rw [Category.assoc, Scheme.isoSpec_hom_naturality (Ss.map a),
          ← Category.assoc, fs.naturality, Category.assoc] }
  let α : B ⟶ (Functor.const Λ).obj (.of A) :=
    { app := fun i ↦ (s.app (Opposite.op i)).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom
      naturality := by
        intro i j a
        change (Ss.map a.op).appTop ≫
          ((s.app (Opposite.op j)).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) =
          ((s.app (Opposite.op i)).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← Scheme.Hom.comp_appTop]
        have hn := s.naturality a.op
        simpa using congrArg (fun t ↦ t.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) hn.symm }
  refine ⟨B, g, α, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hc⟩ := hc
    have hc' := hc.whiskerEquivalence (opOpEquivalence Λ).symm
    exact ⟨IsColimit.ofIsoColimit hc'
      (Cocone.ext (Scheme.ΓSpecIso (.of A)) (by intro i; rfl))⟩
  · intro i
    exact (RingHom.finiteType_algebraMap).mp (hft (Opposite.op i))
  · intro i
    let _ : IsProper (fs.app i) := hp i
    change IsProper (fs.app i ≫ (Ss.obj i).isoSpec.hom)
    infer_instance
  · intro i
    change p.app i ≫ (fs.app i ≫ (Ss.obj i).isoSpec.hom) =
      f ≫ Spec.map ((s.app i).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom)
    rw [← Category.assoc, hw, Category.assoc, Spec.map_comp,
      ← Scheme.isoSpec_Spec_hom]
    congr 1
    exact (Scheme.isoSpec_hom_naturality
      (X := Spec (.of A)) (Y := Ss.obj i) (s.app i)).symm


end AlgebraicGeometry.Scheme
