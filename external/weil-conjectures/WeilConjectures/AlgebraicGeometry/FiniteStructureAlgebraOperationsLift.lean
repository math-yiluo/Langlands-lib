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
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import WeilConjectures.AlgebraicGeometry.FiniteStructureAlgebraAdjointsConstruct

/-! # Algebra structures on algebraized finite direct images

Source: Stacks Project, Tags 09ZT, 088E and 088F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- Lift multiplication and unit and produce the compatible adjoint algebra maps.
Source: Stacks Project, Tag 09ZT, multiplication paragraph, expanded using 088E,
088F and 0CYS. This is the algebra-operations part only; it makes no assertion
about rings of sections or quotient rings.

Proof: Place G on a closed subscheme proper over Spec A whose ideal annihilates G
(0CYS). The ideal annihilates its tensor square and cube as well. These tensor powers
are quasi-coherent and finite type on the Noetherian scheme X, hence coherent.
Transport the finite direct-image multiplications through psi and the tensor-pullback
comparison. The algebra base-change formula and hpsi show their compatibility.
Full faithfulness in 088E lifts this family uniquely to G tensor G -> G. For the
unit, use the quotient structure sheaf on the proper supporting closed subscheme:
its ideal acts trivially on G and on each reduction, so the units factor through
this quotient. This coherent proper-support source permits the same unique lifting.
Faithfulness on the tensor cube, square and G proves associativity, commutativity
and both unit identities. On each open equip G's additive group with this product
and unit. Bilinearity gives distributivity; the identities just proved give a
commutative ring. The restriction maps preserve the operations, and the additive
sheaf condition implies the ring sheaf condition. The lifted unit supplies the
structure map, yielding B and the canonical underlying-module isomorphism e.
The adjoints of the transported psi preserve multiplication and the unit and thus
supply b. Their underlying section maps are exactly the displayed composites of
the tensor-pullback adjunction unit, pullback of e, psi and pushforward composition.
Apply adjunction to hpsi; naturality of its units and the canonical composition
comparison hc identify the two composites with the displayed transition equality.
This equality holds on every open, without an affineness assumption. Empty schemes,
zero modules and empty opens give the zero ring and the same construction. No data
is defined by choosing a witness of mere existence: operations are determined
uniquely by full faithfulness, and B is built explicitly from these operations.
(blueprint: lem-weil-pbc-finite-structure-algebra-operations-lift). -/
theorem finite_structure_algebra_operations_lift
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
        (c n).hom.app G ≫ (ψ n).hom)
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm) :
    ∃ B : X.CommAlgebraSheaf, ∃ e : B.toModule ≅ G,
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens) (x : B.right.obj.obj (op U)),
          ((b n).right.hom.app (op U)).hom x =
            ((Scheme.Modules.pushforwardComp (fnY n) (pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).hom.app
              (SheafOfModules.unit (Yn n).ringCatSheaf)).app U
                (((Scheme.Modules.pushforward (pullback.fst f
                    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map
                  ((Scheme.Modules.tensorPullback (pullback.fst f
                    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map
                      e.hom ≫ (ψ n).hom)).app U
                  (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                    (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1)))))))).unit.app B.toModule).app U x))) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U)) := by
  have H :=
    finite_structure_algebra_adjoints_construct A I X f i hi hp c hc
      Yn fnY gn hcart hw G hG hproper ψ hψ
  rcases H with ⟨B, e, b, hb⟩
  let j := fun n ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let a := fun n ↦ (Scheme.Modules.tensorPullback (j n)).map e.hom ≫ (ψ n).hom
  have ha : ∀ n, (Scheme.Modules.tensorPullback (i n)).map (a (n + 1)) ≫
      (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
        (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
        (Scheme.Modules.pushforward (fnY n)).map
          (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
      (c n).hom.app B.toModule ≫ a n := by
    intro n
    dsimp only [a]
    rw [Functor.map_comp, Category.assoc, hψ]
    rw [← Category.assoc]
    exact congrArg (fun q ↦ q ≫ (ψ n).hom) ((c n).hom.naturality e.hom)
  have ht := Scheme.Modules.finiteStructureAdjoint_transitions X _ Yn j fnY i gn
    hi (fun n ↦ (hcart n).flip.w) hw c hc B.toModule a ha
  refine ⟨B, e, b, ?_, ?_⟩
  · intro n U x
    exact hb n U x
  · intro n U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change ((gn n).appLE _ _ _).hom (((b (n + 1)).right.hom.app (op U)).hom x) =
      ((b n).right.hom.app (op U)).hom x
    rw [hb (n + 1) U x, hb n U x]
    exact ht n U x

end AlgebraicGeometry
