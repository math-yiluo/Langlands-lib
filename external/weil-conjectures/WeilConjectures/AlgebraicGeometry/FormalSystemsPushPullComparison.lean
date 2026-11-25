/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FormalCompletionPushforwardLift
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Construction of the formal push-pull comparison

Source: Stacks Project, Cohomology of Schemes, Lemma 088B, first half of the proof.
(blueprint: lem-weil-pbc-formal-systems-push-pull-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction maps factor through the completed proper pushforward. The first
identity characterizes the quotient comparison `κ`, and the second characterizes `α`.
There is no exceptional ideal or annihilation assertion in this construction.

Source: Stacks Project, Lemma 088B, proof up to the definition of the limit comparison.
(blueprint: lem-weil-pbc-formal-systems-push-pull-comparison)

Proof: The coherence hypothesis makes its completion a coherent formal module. At level n+1,
the pushforward of the quotient projection kills J^(n+1), since this ideal acts
through (J.comap f)^(n+1) on the target. The cokernel universal property gives
κ_n; cancellation of quotient projections gives compatibility with transitions.
The adjunction unit followed by the pushforward of β_n gives compatible maps γ_n.
On each affine open the degree-zero theorem on formal functions identifies the
inverse limit of κ with an isomorphism from the completion of the sections of f_*F.
The affine equivalence for coherent formal modules turns its inverse composed
with the limit of γ into a formal-system map α. The limit projections are
surjective, so κ_n α_n = γ_n, and this equation uniquely determines α on an
affine open. Restricting to a smaller affine open preserves the equations and
therefore the map. Glue the component sheaf maps on the affine basis; their
transition identities and the two asserted equations hold locally, hence globally.
-/
theorem exists_formalSystemsPushPull_comparison {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj)) :
    ∃ κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
          formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f,
        ∃ α : G ⟶ (completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
          (∀ n : ℕ,
            formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
              κ.app (op n) =
            (Scheme.Modules.pushforward f).map
              (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) ∧
          (∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
            adj.unit.app (G.obj.obj (op n)) ≫
              (Scheme.Modules.pushforward f).map (β.hom.app (op n))) := by
  classical
  let T := Scheme.Modules.tensorPullback f
  let P := Scheme.Modules.pushforward f
  let H := P.obj F.obj
  let := adj.isLeftAdjoint
  have hH : H.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y H).mp h |>.1
  have hz (n : ℕ) :
      Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H ≫
        P.map (formalModuleQuotientπ (J.comap f) (n + 1) F.obj) = 0 := by
    let i := Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H
    let j := Scheme.idealModuleProductι
      (Scheme.idealSheafPower (J.comap f).toModulesι (n + 1)).2 (T.obj H)
    let q := formalModuleQuotientπ (J.comap f) (n + 1) F.obj
    have hj : j ≫ adj.counit.app F.obj ≫ q = 0 :=
      formalModuleQuotient_map_zero (J.comap f) (adj.counit.app F.obj)
        (Nat.le_refl (n + 1))
    have himage : imageSubobject (T.map i) = imageSubobject j :=
      modulePullbackIdealPowerProductImage f J H hH (n + 1)
    have hi : T.map i ≫ adj.counit.app F.obj ≫ q = 0 := by
      have hzero : (imageSubobject (T.map i)).arrow ≫ adj.counit.app F.obj ≫ q = 0 := by
        rw [himage]
        exact imageSubobject_arrow_comp_eq_zero hj
      rw [← imageSubobject_arrow_comp (T.map i), Category.assoc, hzero, comp_zero]
    apply (adj.homEquiv _ _).symm.injective
    rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_symm_apply]
    simpa only [Adjunction.homEquiv_symm_apply, Functor.map_zero, zero_comp,
      Category.assoc] using hi
  let k (n : ℕ) := cokernel.desc
    (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H)
    (P.map (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) (hz n)
  have hk (n : ℕ) : formalModuleQuotientπ J (n + 1) H ≫ k n =
      P.map (formalModuleQuotientπ (J.comap f) (n + 1) F.obj) :=
    cokernel.π_desc _ _ _
  have hq {Z : Scheme.{u}} (I : Z.IdealSheafData) {A B : Z.Modules}
      (v : A ⟶ B) {m n : ℕ} (hmn : n ≤ m) :
      formalModuleQuotientπ I m A ≫ formalModuleQuotientMap I v hmn =
        v ≫ formalModuleQuotientπ I n B := cokernel.π_desc _ _ _
  let κ : formalCompletionSystem J H ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ P :=
    { app := fun n ↦ k n.unop
      naturality := by
        intro a b g
        apply (cancel_epi (cokernel.π
          (Scheme.idealModuleProductι
            (Scheme.idealSheafPower J.toModulesι (a.unop + 1)).2 H))).1
        change formalModuleQuotientπ J (a.unop + 1) H ≫
            formalModuleQuotientMap J (𝟙 H) (Nat.succ_le_succ (leOfHom g.unop)) ≫ k b.unop =
          formalModuleQuotientπ J (a.unop + 1) H ≫ k a.unop ≫
            P.map (formalModuleQuotientMap (J.comap f) (𝟙 F.obj)
              (Nat.succ_le_succ (leOfHom g.unop)))
        rw [← Category.assoc, hq]
        rw [Category.id_comp, hk]
        rw [← Category.assoc, hk, ← P.map_comp, hq, Category.id_comp] }
  let γ : G.obj ⟶ formalCompletionSystem (J.comap f) F.obj ⋙ P :=
    { app := fun n ↦ adj.unit.app (G.obj.obj n) ≫ P.map (β.hom.app n)
      naturality := by
        intro a b g
        change G.obj.map g ≫ adj.unit.app (G.obj.obj b) ≫ P.map (β.hom.app b) =
          (adj.unit.app (G.obj.obj a) ≫ P.map (β.hom.app a)) ≫
            P.map ((formalCompletionSystem (J.comap f) F.obj).map g)
        have hu := adj.unit.naturality (G.obj.map g)
        dsimp only [Functor.id_map, Functor.comp_map] at hu
        rw [← Category.assoc, hu, Category.assoc, ← P.map_comp]
        have hβ := β.hom.naturality g
        dsimp only [Functor.comp_map] at hβ
        rw [hβ]
        simp only [P.map_comp, Category.assoc] }
  obtain ⟨α, hα⟩ := formalCompletion_pushforward_lift J f G F h κ hk γ
  refine ⟨κ, α, hk, ?_⟩
  intro n
  exact congrArg (fun a ↦ a.app (op n)) hα

end AlgebraicGeometry
