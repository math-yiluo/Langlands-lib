/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismCategoryEquivalence

@[expose] public section

open CategoryTheory Opposite Limits
universe u v
namespace AlgebraicGeometry.Scheme
/-- The representative-preserving bijection on set-valued stalks.
Source: Stacks Project, Étale Cohomology, Remark 59.29.8, Tag 04FN.
(blueprint: new-geometric-point-morphism-set-stalk)

Proof: The category-equivalence component gives an equivalence of pointed étale
neighbourhoods which preserves the underlying étale object. The source stalk
diagram is therefore the target stalk diagram precomposed with the opposite of
this equivalence. The canonical colimit comparison has the required formula on
coprojections, and it is an isomorphism because an equivalence is final. Equality
on every coprojection proves uniqueness by the colimit universal property.
Every morphism with the formula equals this comparison, so it too is an
isomorphism (and in Type its underlying function is bijective). -/
theorem geometricPointMorphism_set_stalk
    {S : Scheme.{u}} {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
    (a : Spec (.of k) ⟶ Spec (.of k')) (ha : a ≫ s' = s) :
    ∀ F : Sheaf S.smallEtaleTopology (Type (max u v)),
      let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
      let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
        Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
      let P := fun f : (pointSmallEtale s').sheafFiber.obj F →
          (pointSmallEtale s).sheafFiber.obj F ↦
        ∀ (U : S.Etale) (t : (pointSmallEtale s').fiber.obj U)
          (σ : F.obj.obj (op U)),
          f ((pointSmallEtale s').toPresheafFiber U t F.obj σ) =
            (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj σ
      (∃! f, P f) ∧ ∀ f, P f → Function.Bijective f := by
  intro F
  let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
  let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
    Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
  have : (NatTrans.mapElements α).IsEquivalence :=
    geometricPointMorphism_category_equivalence s s' a ha
  let D := (Functor.Elements.π (pointSmallEtale s).fiber).op ⋙ F.obj
  let f : (pointSmallEtale s').sheafFiber.obj F ⟶
      (pointSmallEtale s).sheafFiber.obj F :=
    colimit.pre D (NatTrans.mapElements α).op
  have hf : ∀ U t σ, f ((pointSmallEtale s').toPresheafFiber U t F.obj σ) =
      (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj σ := by
    intro U t σ
    exact ConcreteCategory.congr_hom
      (colimit.ι_pre D (NatTrans.mapElements α).op (op (Functor.elementsMk _ U t))) σ
  have hi : IsIso f := by dsimp [f]; infer_instance
  have hu : ∀ g : (pointSmallEtale s').sheafFiber.obj F →
      (pointSmallEtale s).sheafFiber.obj F,
      (∀ U t σ, g ((pointSmallEtale s').toPresheafFiber U t F.obj σ) =
      (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj σ) → g = f.hom := by
    intro g hg
    have he : TypeCat.ofHom g = f := by
      apply (pointSmallEtale s').presheafFiber_hom_ext
      intro U t
      ext σ
      exact (hg U t σ).trans (hf U t σ).symm
    exact funext (fun x ↦ ConcreteCategory.congr_hom he x)
  exact ⟨⟨f, hf, hu⟩, fun g hg ↦ by
    rw [hu g hg]
    exact (CategoryTheory.isIso_iff_bijective f).mp hi⟩

end AlgebraicGeometry.Scheme
