/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra

/-! # Transition compatibility for adjoints of a module system

Source: Stacks Project, Tags 0093, 0096 and 09ZT.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The explicit adjoint followed by pushforward composition.
Source: Stacks Project, Tags 0093 and 0096
(blueprint: lem-weil-pbc-finite-structure-adjoint-transitions). -/
noncomputable def finiteStructureAdjoint
    {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S) (G : X.Modules)
    (a : (tensorPullback j).obj G ⟶ (pushforward p).obj
      (SheafOfModules.unit Y.ringCatSheaf)) :
    G ⟶ (pushforward (p ≫ j)).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app G ≫
    (pushforward j).map a ≫
      (pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf)

/-- Compatible module maps have compatible adjoints on every open, when the composition
comparison is the mate of the canonical pushforward comparison.
Source: Stacks Project, Tags 0093, 0096 and 09ZT, adjunction step of algebraization.

Proof: Apply the tensor-pullback adjunction for i to the compatibility equation. The
base-change map was defined as the mate of the pushforward of the unit along g. Following
it by the structure-sheaf pullback map gives the pushforward of g's ring map, by the
structure-sheaf adjunction formula. Naturality of the unit for j moves a through that
unit. The specified mate composition comparison identifies the composite unit for j and i
with the unit for their composite, transported along wj. Naturality of the pushforward
composition isomorphisms and the two square equations then identify both composites in
the module category. Evaluate on U and x. Pushforward composition is restriction along
the equality of inverse-image opens, so this is exactly the displayed appLE equation.
The argument uses no affineness, coherence, properness or invertibility of a. On an empty
open both sides are maps to the zero ring, and the same computation applies.
(blueprint: lem-weil-pbc-finite-structure-adjoint-transitions). -/
theorem finiteStructureAdjoint_transitions
    (X : Scheme.{u}) (S Y : ℕ → Scheme.{u})
    (j : ∀ n, S n ⟶ X) (p : ∀ n, Y n ⟶ S n)
    (i : ∀ n, S n ⟶ S (n + 1)) (g : ∀ n, Y n ⟶ Y (n + 1))
    (wj : ∀ n, i n ≫ j (n + 1) = j n)
    (wp : ∀ n, g n ≫ p (n + 1) = p n ≫ i n)
    (w : ∀ n, g n ≫ (p (n + 1) ≫ j (n + 1)) = p n ≫ j n)
    (c : ∀ n, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅ tensorPullback (j n))
    (hc : ∀ n, c n = (tensorPullbackCompositionIso (i n) (j (n + 1)) (j n)
      (wj n)).symm)
    (G : X.Modules)
    (a : ∀ n, (tensorPullback (j n)).obj G ⟶
      (pushforward (p n)).obj (SheafOfModules.unit (Y n).ringCatSheaf))
    (ha : ∀ n, (tensorPullback (i n)).map (a (n + 1)) ≫
      (moduleBaseChangeMap (p (n + 1)) (p n) (i n) (g n) (wp n)
        (SheafOfModules.unit (Y (n + 1)).ringCatSheaf) ≫
        (pushforward (p n)).map (tensorPullbackObjUnitToUnit (g n))) =
      (c n).hom.app G ≫ a n) :
    ∀ (n : ℕ) (U : X.Opens) (x : Γ(G, U)),
      ((g n).appLE ((p (n + 1) ≫ j (n + 1)) ⁻¹ᵁ U) ((p n ≫ j n) ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, w n])).hom
        ((finiteStructureAdjoint (j (n + 1)) (p (n + 1)) G (a (n + 1))).app U x) =
      (finiteStructureAdjoint (j n) (p n) G (a n)).app U x := by
  intro n U x
  let aj := Classical.choose (exists_tensorPullbackAdjunction (j (n + 1)))
  let ai := Classical.choose (exists_tensorPullbackAdjunction (i n))
  let a0 := Classical.choose (exists_tensorPullbackAdjunction (j n))
  let q := pushforwardComp (i n) (j (n + 1)) ≪≫ pushforwardCongr (wj n)
  have hu := unit_conjugateEquiv_symm (aj.comp ai) a0 q.hom G
  have hu' : (aj.comp ai).unit.app G ≫
      q.hom.app ((tensorPullback (j (n + 1)) ⋙ tensorPullback (i n)).obj G) =
    a0.unit.app G ≫ (pushforward (j n)).map ((c n).inv.app G) := by
    simpa only [hc n, Iso.symm_inv, tensorPullbackCompositionIso,
      conjugateIsoEquiv_symm_apply_hom, aj, ai, a0, q] using hu
  have hu'' : (aj.comp ai).unit.app G ≫
      q.hom.app ((tensorPullback (j (n + 1)) ⋙ tensorPullback (i n)).obj G) ≫
      (pushforward (j n)).map ((c n).hom.app G) = a0.unit.app G := by
    rw [← Category.assoc, hu', Category.assoc, ← Functor.map_comp,
      (c n).inv_hom_id_app, CategoryTheory.Functor.map_id]
    exact CategoryTheory.Category.comp_id _
  have hb := moduleBaseChangeMap_algebra (p (n + 1)) (p n) (i n) (g n) (wp n)
  obtain ⟨mu, mu', hm, hm', hbeta, _, _⟩ := hb
  have h := congrArg (fun z ↦
    aj.unit.app G ≫ (pushforward (j (n + 1))).map (ai.homEquiv _ _ z) ≫
      q.hom.app ((pushforward (p n)).obj (SheafOfModules.unit (Y n).ringCatSheaf))) (ha n)
  rw [Adjunction.homEquiv_naturality_left] at h
  simp only [Adjunction.homEquiv_unit] at h
  dsimp only [ai] at h
  rw [hbeta] at h
  have hr : aj.unit.app G ≫ (pushforward (j (n + 1))).map
      (ai.unit.app ((tensorPullback (j (n + 1))).obj G) ≫
        (pushforward (i n)).map ((c n).hom.app G ≫ a n)) ≫
      q.hom.app ((pushforward (p n)).obj (SheafOfModules.unit (Y n).ringCatSheaf)) =
      a0.unit.app G ≫ (pushforward (j n)).map (a n) := by
    calc
      _ = (aj.comp ai).unit.app G ≫
          (pushforward (i n) ⋙ pushforward (j (n + 1))).map
            ((c n).hom.app G ≫ a n) ≫ q.hom.app _ := by
        simp only [Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp,
          CategoryTheory.Functor.comp_map, Category.assoc]
      _ = (aj.comp ai).unit.app G ≫ q.hom.app _ ≫
          (pushforward (j n)).map ((c n).hom.app G ≫ a n) := by
        rw [q.hom.naturality]
      _ = _ := by
        rw [CategoryTheory.Functor.map_comp]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ (pushforward (j n)).map (a n)) hu''
  rw [show Classical.choose (exists_tensorPullbackAdjunction (i n)) = ai from rfl,
    hr] at h
  have he := congrArg (fun z ↦ z.app U x) h
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, q, Iso.trans_hom, NatTrans.comp_app] at he
  simp only [finiteStructureAdjoint, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforwardComp_hom_app_app, pushforward_map_app]
  let hle : (p n) ⁻¹ᵁ ((j n) ⁻¹ᵁ U) ≤
      (g n) ⁻¹ᵁ ((p (n + 1)) ⁻¹ᵁ ((j (n + 1)) ⁻¹ᵁ U)) := by
    change (p n ≫ j n) ⁻¹ᵁ U ≤ (g n ≫ (p (n + 1) ≫ j (n + 1))) ⁻¹ᵁ U
    rw [w n]
  change ((Y n).presheaf.map (homOfLE hle).op).hom
    ((g n).app ((p (n + 1)) ⁻¹ᵁ ((j (n + 1)) ⁻¹ᵁ U))
      ((a (n + 1)).app ((j (n + 1)) ⁻¹ᵁ U) ((aj.unit.app G).app U x))) =
    (a n).app ((j n) ⁻¹ᵁ U) ((a0.unit.app G).app U x)
  change (Y n).presheaf.map _ ((Y n).presheaf.map _
    ((g n).app _ ((a (n + 1)).app _ ((aj.unit.app G).app U x)))) =
    (a n).app _ ((a0.unit.app G).app U x) at he
  rw [← ConcreteCategory.comp_apply, ← (Y n).presheaf.map_comp] at he
  have heq : (homOfLE hle).op =
      (eqToHom (congrArg (fun k : Y n ⟶ S (n + 1) ↦
        k ⁻¹ᵁ ((j (n + 1)) ⁻¹ᵁ U)) (wp n).symm)).op ≫
      (TopologicalSpace.Opens.map (p n).base).op.map
        (eqToHom (congrArg (fun k : S n ⟶ X ↦ k ⁻¹ᵁ U) (wj n).symm)).op :=
    Subsingleton.elim _ _
  rw [heq]
  exact he

end AlgebraicGeometry.Scheme.Modules
