/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechScalarChainAction

/-! # Coefficient endomorphisms on additive Čech complexes

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical cocycle comparison is natural for a coefficient endomorphism.
Source: Stacks Project, Tag 01EQ, and the injective-resolution Ext construction.
(blueprint: new-q4-additive-cech-global-map-naturality)

Proof: Represent the cycle by the constant-free-sheaf morphism corresponding
under constantSheafAdj and uliftZMultiplesAddEquiv. Its differential is zero
because iCycles maps into the kernel. The resolution comparison sends this
morphism to its composite with desc(f).f n, by naturality of that adjunction.
Apply global_cocycle to both representing cycles. The identity extMk_comp_mk₀
for the augmentation-preserving resolution morphism identifies their Ext
classes; the latter composite with Ext.mk₀ f is exactly Sheaf.H.map f n.
This holds in degree zero as well, with the same cocycle formula. -/
theorem additiveCech_global_map_naturality
    (X : Scheme.{u}) (I : InjectiveResolution X.etaleAdditiveSheaf)
    (c : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (f : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf) (n : ℕ)
    (s : (additiveCechGlobal I).cycles n) :
    c.globalEquiv n ((additiveCechGlobal I).homologyπ n
      (HomologicalComplex.cyclesMap (additiveCechGlobalMap I f) n s)) =
      Sheaf.H.map f n (c.globalEquiv n ((additiveCechGlobal I).homologyπ n s)) := by
  let K := additiveCechGlobal I
  let G := additiveCechGlobalMap I f
  let d := InjectiveResolution.desc f I I
  let e := fun k ↦ ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ (I.cocomplex.X k)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let a := (e n).symm (K.iCycles n s)
  have ha : a ≫ I.cocomplex.d n (n + 1) = 0 := by
    apply (e (n + 1)).injective
    change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (((constantSheafAdj _ _ _).homAddEquiv _ _) (a ≫ I.cocomplex.d n (n + 1))) = _
    simp only [Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    change (K.d n (n + 1)) (e n a) = _
    rw [AddEquiv.apply_symm_apply]
    have hs := ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) s
    simpa only [ConcreteCategory.comp_apply, map_zero, AddCommGrpCat.zero_apply] using hs
  let a' := a ≫ d.f n
  have ha' : a' ≫ I.cocomplex.d n (n + 1) = 0 := by
    dsimp only [a']
    rw [Category.assoc, d.comm n (n + 1), ← Category.assoc, ha, zero_comp]
  have hrep : K.iCycles n (HomologicalComplex.cyclesMap G n s) = e n a' := by
    have hs := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i G n) s
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hs
    rw [hs]
    change _ = AddCommGrpCat.uliftZMultiplesAddEquiv _
      (((constantSheafAdj _ _ _).homAddEquiv _ _) (a ≫ d.f n))
    simp only [Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    change _ = G.f n (e n ((e n).symm _))
    rw [AddEquiv.apply_symm_apply]
  rw [c.global_cocycle n a' ha' _ hrep]
  rw [c.global_cocycle n a ha s (by exact ((e n).apply_symm_apply _).symm)]
  let φ : I.Hom I f :=
    { hom := d
      ι_f_zero_comp_hom_f_zero := by
        exact InjectiveResolution.desc_commutes_zero f I I }
  rw [Sheaf.H.map_apply]
  exact (I.extMk_comp_mk₀ a (n + 1) rfl ha φ).symm

end AlgebraicGeometry.Scheme.Modules
