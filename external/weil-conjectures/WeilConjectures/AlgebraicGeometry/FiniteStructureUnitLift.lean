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

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions
import WeilConjectures.AlgebraicGeometry.FiniteStructureUnitLiftExistence

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Lift the unit of finite structure sheaves

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-unit-lift).
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

/-- Lift the unit through a proper supporting quotient, and prove its left unit law.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, expanded using 088E, 088F
and 0CYS.

Proof: Let J be an ideal sheaf annihilating G whose closed subscheme is proper over A.
The quotient O_X/J is coherent and has proper support. After reduction, J annihilates
p_n,* O_Yn via ψ, so the structure map to this algebra factors through the reduced
quotient. These factorizations commute with transitions, since the base-change map
preserves the structure map and the pinned composition comparison preserves units.
Full faithfulness lifts the factorizations uniquely to a map O_X/J to G. Compose with
the quotient map to define η. The adjunction unit and pushforward composition give the
stated scalar formula. Multiplicativity of the given μ and this formula identify the
completed left-unit composite with the identity of G; faithfulness on G proves the left
unit law. For uniqueness, if η and η' both satisfy the left unit law, then on each open
μ(η(1),η'(1)) equals η'(1) by the first law and η(1) by symmetry and the second law.
Thus η(1)=η'(1); linearity gives η(r)=rη(1)=rη'(1)=η'(r). Sectionwise extensionality
proves equality of the module morphisms. No properness of O_X itself is assumed.
For the zero algebra or an empty scheme all maps are the unique zero maps.
(blueprint: lem-weil-pbc-finite-structure-unit-lift). -/
theorem finite_structure_unit_lift
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
        (c n).hom.app G ≫ (ψ n).hom)
    (μ : G ⊗ G ⟶ G)
    (hcomm : ∀ (U : X.Opens) (x y : Γ(G, U)),
      μ.app U (tmulSection x y) = μ.app U (tmulSection y x))
    (hμ : ∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
          fun x ↦ (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
        ∀ (x y : Γ(G, U)),
          a (μ.app U (tmulSection x y)) = a x * a y) :
    ∃! η : SheafOfModules.unit X.ringCatSheaf ⟶ G,
      (∀ (U : X.Opens) (x : Γ(G, U)),
        μ.app U (tmulSection ((η.val.app (op U)).hom (1 : Γ(X, U))) x) = x) ∧
      (∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          ((η.val.app (op U)).hom r) =
          (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))).app U r) := by
  obtain ⟨η, hη⟩ := finite_structure_unit_lift_existence A I X f i hi hp c hc Yn fnY gn
    hcart hw G hG hproper ψ hψ μ hcomm hμ
  refine ⟨η, hη, ?_⟩
  intro η' hη'
  apply SheafOfModules.hom_ext
  ext U
  let V : X.Opens := unop U
  let one : Γ(G, V) := (η.val.app U).hom (1 : Γ(X, V))
  let one' : Γ(G, V) := (η'.val.app U).hom (1 : Γ(X, V))
  have h1 := hη'.1 V one
  have h2 := hη.1 V one'
  have hc := hcomm V one one'
  simp only [one, one'] at h1 h2
  have heq : one' = one := by
    calc
      one' = μ.app V (tmulSection one one') := by symm; exact h2
      _ = μ.app V (tmulSection one' one) := hc
      _ = one := h1
  change (η'.val.app U).hom (1 : Γ(X, V)) = (η.val.app U).hom (1 : Γ(X, V))
  simpa [one, one'] using heq


end AlgebraicGeometry
