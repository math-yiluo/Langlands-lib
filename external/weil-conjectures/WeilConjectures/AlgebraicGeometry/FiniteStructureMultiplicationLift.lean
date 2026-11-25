/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.FiniteStructureProductExists
import WeilConjectures.AlgebraicGeometry.FiniteStructureTensorTestsFaithful

/-! # Lift multiplication of finite structure sheaves

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-multiplication-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- Lift multiplication, with associativity and symmetry, but without a unit or algebra sheaf.
Source: Stacks Project, Tag 09ZT, multiplication paragraph, using 088E, 088F and 0CYS.

Proof: Choose a proper closed subscheme annihilating G. Its ideal annihilates both tensor
powers of G; quasi-coherence and finite type imply coherence of the square and cube.
Transport the multiplication of each finite direct image through ψ and the tensor-pullback
comparison. The canonical composition comparison preserves elementary tensor sections by
its pinned-adjunction mate formula. The base-change multiplication formula and hψ give the
compatibility equation. Full faithfulness of completion lifts this family uniquely to μ.
The two associativity composites on the tensor cube and the two symmetry composites on
the square agree after completion, where they are the ring laws of O_Yn. Faithfulness makes
them equal on X. Evaluation on elementary section tensors gives the displayed laws.
The pullback tensor comparison carries pulled-back elementary tensors to their tensor
product. Evaluating the lifted multiplication under the adjunction unit and pushforward
composition therefore gives the displayed multiplicativity of every adjoint. For uniqueness,
that formula determines the completed multiplication on local generators of pullback;
full faithfulness then determines μ. Zero modules and empty schemes use the same argument.
(blueprint: lem-weil-pbc-finite-structure-multiplication-lift). -/
theorem finite_structure_multiplication_lift
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃! μ : G ⊗ G ⟶ G,
      (∀ (U : X.Opens) (x y z : Γ(G, U)),
        μ.app U (tmulSection (μ.app U (tmulSection x y)) z) =
          μ.app U (tmulSection x (μ.app U (tmulSection y z)))) ∧
      (∀ (U : X.Opens) (x y : Γ(G, U)),
        μ.app U (tmulSection x y) = μ.app U (tmulSection y x)) ∧
      (∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
          fun x ↦ (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
        ∀ (x y : Γ(G, U)),
          a (μ.app U (tmulSection x y)) = a x * a y) := by
  obtain ⟨μ, hμ⟩ := finite_structure_product_exists_core A I X f i hi hp c hc
    Yn fnY gn hcart hw G hG hproper ψ hψ
  obtain ⟨hsquare, hcube⟩ := finite_structure_tensor_tests_faithful A I X f i hi hp
    Yn fnY G hG hproper ψ
  dsimp only at hμ
  have hcomm : (β_ G G).hom ≫ μ = μ := by
    apply hsquare
    intro n U x y
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      braiding_hom_app_tmulSection]
    rw [hμ n U y x, hμ n U x y, mul_comm]
  have hassoc : (μ ▷ G) ≫ μ = (α_ G G G).hom ≫ (G ◁ μ) ≫ μ := by
    apply hcube
    intro n U x y z
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection, associator_hom_app_tmulSection,
      whiskerLeft_app_tmulSection]
    rw [hμ n U, hμ n U, hμ n U, hμ n U, mul_assoc]
  refine ⟨μ, ⟨?_, ?_, hμ⟩, ?_⟩
  · intro U x y z
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection, associator_hom_app_tmulSection,
      whiskerLeft_app_tmulSection] using
      congrArg (fun v : (G ⊗ G) ⊗ G ⟶ G ↦ v.app U (tmulSection (tmulSection x y) z))
        hassoc
  · intro U x y
    exact (congrArg (fun v : G ⊗ G ⟶ G ↦ v.app U (tmulSection x y)) hcomm).symm.trans
      (by simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        braiding_hom_app_tmulSection])
  · intro ν hν
    apply hsquare
    intro n U x y
    exact (hν.2.2 n U x y).trans (hμ n U x y).symm


end AlgebraicGeometry
