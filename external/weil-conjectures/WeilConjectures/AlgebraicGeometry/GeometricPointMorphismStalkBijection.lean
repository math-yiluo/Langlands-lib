/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismCategoryEquivalence
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismSetStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismAddCommGrpStalk

/-!
# Morphisms of geometric points and étale stalks

Source: Stacks Project, Étale Cohomology, Remark 59.29.8, Tag 04FN
(blueprint: lem-weil-pbc-geometric-point-morphism-stalk-bijection).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A morphism of geometric points induces the indicated equivalence of pointed étale
neighbourhoods and the unique representative-preserving bijection on set-valued stalks;
for abelian sheaves the representative-preserving morphism is an isomorphism.
Source: Stacks Project, Étale Cohomology, Remark 59.29.8, Tag 04FN
(blueprint: lem-weil-pbc-geometric-point-morphism-stalk-bijection).

Proof: (1) By lem-weil-pbc-morphism-from-spec-field, write maps from a field spectrum as
pairs of a point and a residue-field embedding. lem-weil-pbc-residue-field-point-naturality and
lem-weil-pbc-spec-field-point-residue-field identify `a` with `Spec α` for an injective
field map `α : k' → k`; precomposition with `a` is injective on maps to any scheme.
(2) Lifts to an étale `U` are residue-field embeddings over the same point of `S`, and
precomposition replaces an embedding `φ'` by `α ∘ φ'`.
(3) By lem-weil-pbc-etale-residue-field-extension-separable the étale residue-field
extension is separable algebraic. Every element in the image of a lift into `k` is
algebraic over `α(k')`, hence lies in `α(k')` since `k'` is
algebraically closed (lem-weil-pbc-algebraic-over-algebraically-closed-subfield).
Thus each lift factors uniquely through `α`, giving bijectivity on pointed objects.
(4) Injectivity of precomposition gives bijections on all morphisms, so the functor of
pointed neighbourhoods is an equivalence compatible with forgetting the lift.
(5) By def-weil-pbc-geometric-stalks the stalk is the colimit over opposite pointed
neighbourhoods. Its universal property constructs the map with the displayed
rule on representatives and proves uniqueness. The inverse equivalence constructs its
inverse on representatives. For abelian sheaves, the same colimit construction is additive;
definition-torsion-sheaves--3 makes the colimits filtered,
so they have the corresponding underlying sets and the map is an isomorphism. -/
theorem geometricPointMorphism_stalk_bijection
    {S : Scheme.{u}} {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
    (a : Spec (.of k) ⟶ Spec (.of k')) (ha : a ≫ s' = s) :
    let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
    let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
      Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
    (NatTrans.mapElements α).IsEquivalence ∧
    (∀ F : Sheaf S.smallEtaleTopology (Type (max u v)),
      let P := fun f : (pointSmallEtale s').sheafFiber.obj F →
          (pointSmallEtale s).sheafFiber.obj F ↦
        ∀ (U : S.Etale) (t : (pointSmallEtale s').fiber.obj U)
          (σ : F.obj.obj (op U)),
          f ((pointSmallEtale s').toPresheafFiber U t F.obj σ) =
            (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj σ
      (∃! f, P f) ∧ ∀ f, P f → Function.Bijective f) ∧
    (∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u v},
      let P := fun f : (pointSmallEtale s').sheafFiber.obj F ⟶
          (pointSmallEtale s).sheafFiber.obj F ↦
        ∀ (U : S.Etale) (t : (pointSmallEtale s').fiber.obj U),
          (pointSmallEtale s').toPresheafFiber U t F.obj ≫ f =
            (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj
      (∃! f, P f) ∧ ∀ f, P f → IsIso f) := by
  dsimp
  refine ⟨geometricPointMorphism_category_equivalence s s' a ha, ?_, ?_⟩
  · exact geometricPointMorphism_set_stalk s s' a ha
  · exact geometricPointMorphism_addCommGrp_stalk s s' a ha

end AlgebraicGeometry.Scheme
