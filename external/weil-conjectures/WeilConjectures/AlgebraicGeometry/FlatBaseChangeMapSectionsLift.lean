/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # FlatBaseChangeMapSectionsLift

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe u v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

private theorem augmentedLift {C : Type u} [Category.{v} C] [Abelian C]
    {F : C} (I : InjectiveResolution F) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    ∃ t : I.cocomplex ⟶ K, I.ι.f 0 ≫ t.f 0 = a := by
  let z := Injective.factorThru a (I.ι.f 0)
  have hz : I.ι.f 0 ≫ z = a := Injective.comp_factorThru _ _
  let o := I.exact₀.descToInjective (z ≫ K.d 0 1) (by
    change I.ι.f 0 ≫ (z ≫ K.d 0 1) = 0
    rw [← Category.assoc, hz, ha])
  have ho : I.cocomplex.d 0 1 ≫ o = z ≫ K.d 0 1 :=
    I.exact₀.comp_descToInjective _ _
  let step (n : ℕ)
      (w : Σ' (a : I.cocomplex.X n ⟶ K.X n)
        (b : I.cocomplex.X (n + 1) ⟶ K.X (n + 1)),
          a ≫ K.d n (n + 1) = I.cocomplex.d n (n + 1) ≫ b) :
      Σ' c : I.cocomplex.X (n + 2) ⟶ K.X (n + 2),
        w.2.1 ≫ K.d (n + 1) (n + 2) = I.cocomplex.d (n + 1) (n + 2) ≫ c := by
    let c := (I.exact_succ n).descToInjective
      (w.2.1 ≫ K.d (n + 1) (n + 2)) (by
        dsimp
        rw [← Category.assoc, ← w.2.2, Category.assoc, K.d_comp_d, comp_zero])
    exact ⟨c, ((I.exact_succ n).comp_descToInjective _ _).symm⟩
  refine ⟨CochainComplex.mkHom _ _ z o ho.symm step, ?_⟩
  simpa only [CochainComplex.mkHom_f_0] using hz

namespace AlgebraicGeometry.Scheme.Modules
universe uBC
/-- An augmented flat-pushforward lift exists by degreewise extension into injectives.
Source: Stacks, Tag 02N7. (blueprint: lem-weil-pbc-flat-base-change-lift)
Extend in degree zero across the monic resolution augmentation. Its composite with
 the next differential vanishes on F, so exactness allows extension in degree one.
Repeat using exactness in each positive degree and the equation d²=0. -/
theorem flatBaseChangeResolutionLift {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat (pullback.snd g f)]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) :
    ∃ t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex,
      I.ι.f 0 ≫ t.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
          (pushforward (pullback.snd g f)).map (J.ι.f 0) := by
  let P := pushforward (pullback.snd g f)
  have : P.PreservesInjectiveObjects :=
    (flat_module_pullback_exact_pushforward_injective (pullback.snd g f)).2
  have : ∀ n, Injective (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      J.cocomplex).X n) := fun n ↦ P.injective_obj (J.cocomplex.X n)
  apply augmentedLift
  change _ ≫ (P.map (J.ι.f 0) ≫ P.map (J.cocomplex.d 0 1)) = 0
  rw [← P.map_comp, J.ι_f_zero_comp_complex_d, P.map_zero, comp_zero]

end AlgebraicGeometry.Scheme.Modules
