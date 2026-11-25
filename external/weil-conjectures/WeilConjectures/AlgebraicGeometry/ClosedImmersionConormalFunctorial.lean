/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-!
# Functoriality of conormal sheaves of closed immersions

Source: Stacks Project, Morphisms, Lemma 01R4, Definition 01R2 and Lemma 01R3
(blueprint: lem-weil-pbc-closed-immersion-conormal-functorial).
-/

@[expose] public section

universe uc

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The extended ideal is contained in the ideal of the source closed subscheme.
The map `γ` is fixed by its values on pullbacks of ideal sections. The unique map `c`
is the pullback of `γ`, expressed by the equality of its adjoint with the composite
of the units and `γ`; pushforward comparison maps implement the commutative square.
The affine clause uses ideal sections before their conormal classes: by
`affine_conormal_sections`, the units on these sections are precisely `a mod I²`.
The final affine equation explicitly sends that class to the class of `g.appLE` applied
to its ideal representative. The existential section `s` also records ideal containment
on these affine opens, without choosing coordinates or a second conormal definition.

Source: Stacks Project, Morphisms, Lemma 01R4 (closed immersion case), with 01R2 and 01R3
(blueprint: lem-weil-pbc-closed-immersion-conormal-functorial).
Proof:
1. The Galois connection for ideal comap/map and the kernel of a composite give
   `i'.ker.comap g ≤ i.ker` from the commutative square.
2. The source library's `pullbackToModulesι` factors through the extended ideal by
   its kernel universal property. Ideal containment gives a second kernel lift into
   `i.ker.toModules`. Compare the tensor pullback with Mathlib's pullback by uniqueness
   of left adjoints; its unit equation gives exactly the section formula for `γ`.
3. Compose the adjunctions for `i'` and `f`, then transport the right adjoint through
   `pushforwardComp` and the equality of the two composites. Apply its inverse Hom
   equivalence to the displayed right-hand morphism to construct `c`. Bijectivity of
   this Hom equivalence proves uniqueness already from the adjoint equation.
4. Restrict the section obtained by applying `γ` to the unit of `s'` to `U`. Naturality
   of the ideal inclusion gives its required `g.appLE` value. The adjoint equation for
   `c`, followed by naturality of the unit along `i`, gives the affine equation.
   Thus no affine tensor-generation or quotient calculation is needed for this
   statement, which expresses the affine classes through the pullback units. -/
theorem closedImmersion_conormal_functorial
    {X Z X' Z' : Scheme.{uc}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i') :
    i'.ker.comap g ≤ i.ker ∧
      ∃ γ : (tensorPullback g).obj i'.ker.toModules ⟶ i.ker.toModules,
        (∀ (U' : X'.Opens) (s' : Γ(i'.ker.toModules, U')),
          i.ker.toModulesι.app (g ⁻¹ᵁ U')
              (γ.app (g ⁻¹ᵁ U')
                (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
                  i'.ker.toModules).app U' s')) =
            g.app U' (i'.ker.toModulesι.app U' s')) ∧
        ∃! c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
            (tensorPullback i).obj i.ker.toModules,
          (((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
              i'.ker.toModules) ≫
            (pushforward i').map
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                ((tensorPullback i').obj i'.ker.toModules)) ≫ (pushforward f).map c) ≫
            (pushforwardComp f i').hom.app ((tensorPullback i).obj i.ker.toModules) ≫
            (pushforwardCongr h.symm).hom.app ((tensorPullback i).obj i.ker.toModules) =
          ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
              i'.ker.toModules) ≫
            (pushforward g).map
              (γ ≫ ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules)) ≫
            (pushforwardComp i g).hom.app ((tensorPullback i).obj i.ker.toModules)) ∧
          ∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)
            (s' : Γ(i'.ker.toModules, U'.1)),
            ∃ s : Γ(i.ker.toModules, U.1),
              i.ker.toModulesι.app U.1 s = g.appLE U'.1 U.1 H
                (i'.ker.toModulesι.app U'.1 s') ∧
              ((tensorPullback i).obj i.ker.toModules).val.map
                (homOfLE (i.preimage_mono H)).op
                ((((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
                    i'.ker.toModules) ≫
                  (pushforward i').map
                    (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                      ((tensorPullback i').obj i'.ker.toModules)) ≫
                        (pushforward f).map c) ≫
                  (pushforwardComp f i').hom.app ((tensorPullback i).obj i.ker.toModules) ≫
                  (pushforwardCongr h.symm).hom.app
                    ((tensorPullback i).obj i.ker.toModules)).app U'.1 s') =
                ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).app U.1 s := by
  classical
  have hle : i'.ker.comap g ≤ i.ker := by
    rw [← IdealSheafData.le_map_iff_comap_le, IdealSheafData.map_ker, h]
    exact f.le_ker_comp i'
  refine ⟨hle, ?_⟩
  let J := i'.ker
  let K := J.comap g
  let adjg := Classical.choose (exists_tensorPullbackAdjunction g)
  let e := adjg.leftAdjointUniq (pullbackPushforwardAdjunction g)
  let a : (pullback g).obj J.toModules ⟶ K.toModules :=
    kernel.lift _ (J.pullbackToModulesι g)
      (J.pullbackToModulesι_comp_toPushforwardSubscheme g)
  have ha : a ≫ K.toModulesι = J.pullbackToModulesι g := kernel.lift_ι _ _ _
  have hb : K.toModulesι ≫ i.ker.toPushforwardSubscheme = 0 := by
    apply hom_ext
    intro W
    ext m
    have hm : K.subschemeι.app W (K.toModulesι.app W m) = 0 :=
      (K.range_toModulesι_app_eq W).subset ⟨m, rfl⟩
    have key : ∀ φ : i.ker.subscheme ⟶ X, φ = i.ker.subschemeι →
        φ.app W (K.toModulesι.app W m) = 0 →
        i.ker.subschemeι.app W (K.toModulesι.app W m) = 0 := by
      rintro φ rfl hv
      exact hv
    change i.ker.subschemeι.app W (K.toModulesι.app W m) = 0
    refine key _ (IdealSheafData.inclusion_subschemeι hle) ?_
    change (IdealSheafData.inclusion hle).app (K.subschemeι ⁻¹ᵁ W)
      (K.subschemeι.app W (K.toModulesι.app W m)) = 0
    rw [hm, map_zero]
  let b : K.toModules ⟶ i.ker.toModules := kernel.lift _ K.toModulesι hb
  have hb' : b ≫ i.ker.toModulesι = K.toModulesι := kernel.lift_ι _ _ _
  let γ : (tensorPullback g).obj J.toModules ⟶ i.ker.toModules :=
    e.hom.app J.toModules ≫ a ≫ b
  have hγ (U' : X'.Opens) (s' : Γ(J.toModules, U')) :
      i.ker.toModulesι.app (g ⁻¹ᵁ U')
        (γ.app (g ⁻¹ᵁ U') ((adjg.unit.app J.toModules).app U' s')) =
          g.app U' (J.toModulesι.app U' s') := by
    have he := Adjunction.unit_leftAdjointUniq_hom_app adjg
      (pullbackPushforwardAdjunction g) J.toModules
    have hes := congrArg (fun q ↦ q.app U' s') he
    change (e.hom.app J.toModules).app (g ⁻¹ᵁ U')
      ((adjg.unit.app J.toModules).app U' s') =
        ((pullbackPushforwardAdjunction g).unit.app J.toModules).app U' s' at hes
    have hmap : γ ≫ i.ker.toModulesι =
        e.hom.app J.toModules ≫ J.pullbackToModulesι g := by
      dsimp only [γ]
      simp only [Category.assoc]
      rw [hb', ha]
    have hv := congrArg (fun q ↦ q.app (g ⁻¹ᵁ U')
      ((adjg.unit.app J.toModules).app U' s')) hmap
    change i.ker.toModulesι.app (g ⁻¹ᵁ U')
      (γ.app (g ⁻¹ᵁ U') ((adjg.unit.app J.toModules).app U' s')) =
        (J.pullbackToModulesι g).app (g ⁻¹ᵁ U')
          ((e.hom.app J.toModules).app (g ⁻¹ᵁ U')
            ((adjg.unit.app J.toModules).app U' s')) at hv
    rw [hes] at hv
    exact hv.trans (J.pullbackToModulesι_app_unit g U' s')
  refine ⟨γ, hγ, ?_⟩
  let adjf := Classical.choose (exists_tensorPullbackAdjunction f)
  let adji' := Classical.choose (exists_tensorPullbackAdjunction i')
  let adji := Classical.choose (exists_tensorPullbackAdjunction i)
  let N := (tensorPullback i).obj i.ker.toModules
  let q := pushforwardComp f i' ≪≫ pushforwardCongr h.symm
  let adj := (adji'.comp adjf).ofNatIsoRight q
  let t : J.toModules ⟶ (pushforward (i ≫ g)).obj N :=
    adjg.unit.app J.toModules ≫
      (pushforward g).map (γ ≫ adji.unit.app i.ker.toModules) ≫
      (pushforwardComp i g).hom.app N
  let c := (adj.homEquiv J.toModules N).symm t
  have hc : adj.homEquiv J.toModules N c = t := Equiv.apply_symm_apply _ _
  have heq (d : (tensorPullback f).obj ((tensorPullback i').obj J.toModules) ⟶ N) :
      adj.homEquiv J.toModules N d =
        adji'.unit.app J.toModules ≫
          (pushforward i').map (adjf.unit.app ((tensorPullback i').obj J.toModules) ≫
            (pushforward f).map d) ≫
          (pushforwardComp f i').hom.app N ≫
          (pushforwardCongr h.symm).hom.app N := by
    change ((adji'.comp adjf).ofNatIsoRight q).homEquiv _ _ d = _
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change adji'.homEquiv _ _ (adjf.homEquiv _ _ d) ≫ q.hom.app N = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [q, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have hc' :
      adji'.unit.app J.toModules ≫
        (pushforward i').map (adjf.unit.app ((tensorPullback i').obj J.toModules) ≫
          (pushforward f).map c) ≫
        (pushforwardComp f i').hom.app N ≫
        (pushforwardCongr h.symm).hom.app N = t := by
    exact (heq c).symm.trans hc
  refine ⟨c, ⟨hc', ?_⟩, ?_⟩
  · intro U U' H s'
    let s : Γ(i.ker.toModules, U.1) :=
      i.ker.toModules.presheaf.map (homOfLE H).op
        (γ.app (g ⁻¹ᵁ U'.1) ((adjg.unit.app J.toModules).app U'.1 s'))
    refine ⟨s, ?_, ?_⟩
    · rw [Hom.app_presheaf_map, hγ]
      rfl
    · rw [hc']
      have hu := (adji.unit.app i.ker.toModules).val.naturality (homOfLE H).op
      have hus := congrArg (fun q ↦ q
        (γ.app (g ⁻¹ᵁ U'.1) ((adjg.unit.app J.toModules).app U'.1 s'))) hu
      simp only [t, Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
        ConcreteCategory.comp_apply]
      exact hus.symm
  · intro c' hc''
    apply (adj.homEquiv J.toModules N).injective
    calc
      adj.homEquiv J.toModules N c' = t := by
        exact (heq c').trans hc''.1
      _ = adj.homEquiv J.toModules N c := hc.symm

end AlgebraicGeometry.Scheme.Modules
