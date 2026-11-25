/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # The ordinary map underlying resolution base change

Source: Stacks Project, Tag 02N7, augmentation diagram.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem map_homologyπ {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] :
    (S.map L).homologyπ ≫ (S.mapHomologyIso L).hom =
      (S.mapCyclesIso L).hom ≫ L.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq S.leftHomologyData L]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ShortComplex.LeftHomologyData.map_π]
  rw [Category.assoc, ← L.map_comp]
  simp only [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
    ShortComplex.LeftHomologyData.cyclesIso, ShortComplex.cyclesMapIso',
    ShortComplex.cyclesMap'_id, Iso.refl_inv, Category.id_comp,
    ShortComplex.mapCyclesIso]

private theorem augmented_homology {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (K : CochainComplex C ℕ) (K' : CochainComplex D ℕ)
    {A : C} {B : D} (a : A ⟶ K.cycles 0) (b : B ⟶ K'.cycles 0)
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K')
    (v : L.obj A ⟶ B)
    (h : L.map (a ≫ K.iCycles 0) ≫ φ.f 0 = v ≫ b ≫ K'.iCycles 0) :
    L.map (a ≫ K.homologyπ 0) ≫ ((K.sc 0).mapHomologyIso L).inv ≫
        HomologicalComplex.homologyMap φ 0 = v ≫ b ≫ K'.homologyπ 0 := by
  have hπ : L.map (K.homologyπ 0) ≫ ((K.sc 0).mapHomologyIso L).inv =
      ((K.sc 0).mapCyclesIso L).inv ≫
        ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 0 := by
    change L.map (K.sc 0).homologyπ ≫ ((K.sc 0).mapHomologyIso L).inv =
      ((K.sc 0).mapCyclesIso L).inv ≫ ((K.sc 0).map L).homologyπ
    rw [← cancel_epi ((K.sc 0).mapCyclesIso L).hom]
    rw [← Category.assoc, ← map_homologyπ]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hc : L.map a ≫ ((K.sc 0).mapCyclesIso L).inv ≫
        HomologicalComplex.cyclesMap φ 0 = v ≫ b := by
    apply (cancel_mono (K'.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    change L.map a ≫ ((K.sc 0).mapCyclesIso L).inv ≫
        ((K.sc 0).map L).iCycles ≫ φ.f 0 = _
    erw [← ShortComplex.mapCyclesIso_hom_iCycles]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← L.map_comp]
    exact h
  rw [L.map_comp, Category.assoc]
  erw [reassoc_of% hπ]
  rw [HomologicalComplex.homologyπ_naturality]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ K'.homologyπ 0) hc

namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The degree-zero resolution comparison agrees with ordinary base change under
canonical zeroth-derived-functor identifications.
Source: Stacks Project, Tag 02N7, the augmentation diagram defining the comparison.
(blueprint: lem-weil-pbc-flat-base-change-resolution-degree-zero).

Proof: The augmentation equation for t, after applying pushforward f and the
pushforward square, identifies the degree-zero component of Q on the augmentation
with the pushforward of the q-unit followed by that square and the target
augmentation. Transpose this equality under the g-adjunction. Naturality of its
Hom equivalence identifies the degree-zero component of C on the pulled-back
augmentation with moduleBaseChangeMap followed by the target augmentation.
The augmentations identify the ordinary modules with the degree-zero cycles of
the two pushed-forward resolutions, since pushforward preserves finite limits.
Flat pullback preserves these kernels and homology. Pass the augmentation equation
to degree-zero homology and cancel the resolution-computation isomorphisms. The
canonical map to the zeroth right derived functor is exactly the augmentation
followed by the cycles-to-homology map, so this gives the displayed equality.
No quasi-coherence or properness is required. For zero modules and empty schemes
these same kernel and augmentation identities apply. -/
theorem flatBaseChangeResolutionBeta_degree_zero
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0)) :
    (tensorPullback g).map ((pushforward f).toRightDerivedZero.app F) ≫
        flatBaseChangeResolutionBeta f g I J t 0 =
      moduleBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition.symm F ≫
          (pushforward (pullback.fst g f)).toRightDerivedZero.app
            ((tensorPullback (pullback.snd g f)).obj F) := by
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let K' := ((pushforward (pullback.fst g f)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj J.cocomplex
  let β := moduleBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
    pullback.condition.symm F
  have hC : (tensorPullback g).map ((pushforward f).map (I.ι.f 0)) ≫
      (flatBaseChangeResolutionC f g I J t).f 0 =
        β ≫ (pushforward (pullback.fst g f)).map (J.ι.f 0) := by
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    have hcomponent : adj.homEquiv _ _ ((flatBaseChangeResolutionC f g I J t).f 0) =
        (flatBaseChangeResolutionQ f g I J t).f 0 := by
      have hh := ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv _ _).apply_symm_apply
        (flatBaseChangeResolutionQ f g I J t)
      have hh0 := congrArg (fun z ↦ z.f 0) hh
      simpa only [Adjunction.homEquiv_unit, flatBaseChangeResolutionC,
        Adjunction.mapHomologicalComplex, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f] using hh0
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    erw [hcomponent]
    dsimp only [β, moduleBaseChangeMap, adj, CochainComplex.single₀_obj_zero]
    erw [Equiv.apply_symm_apply]
    let e := flatBaseChangePushforwardSquare f g
    change (pushforward f).map (I.ι.f 0) ≫ (pushforward f).map (t.f 0) ≫
        e.hom.app (J.cocomplex.X 0) =
      (pushforward f).map
          ((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F) ≫
        e.hom.app ((tensorPullback (pullback.snd g f)).obj F) ≫
          (pushforward g).map ((pushforward (pullback.fst g f)).map (J.ι.f 0))
    rw [← (pushforward f).map_comp_assoc, ht, (pushforward f).map_comp, Category.assoc]
    congr 1
    exact e.hom.naturality (J.ι.f 0)
  have hh := augmented_homology (tensorPullback g) K K'
    (I.toRightDerivedZero' (pushforward f))
    (J.toRightDerivedZero' (pushforward (pullback.fst g f)))
    (flatBaseChangeResolutionC f g I J t) β (by
      simpa only [K, K', Category.assoc,
        InjectiveResolution.toRightDerivedZero'_comp_iCycles] using hC)
  rw [I.toRightDerivedZero_eq, J.toRightDerivedZero_eq]
  unfold flatBaseChangeResolutionBeta
  simp only [Functor.map_comp, Category.assoc]
  have hcancel : (tensorPullback g).map (I.isoRightDerivedObj (pushforward f) 0).inv ≫
      (tensorPullback g).map (I.isoRightDerivedObj (pushforward f) 0).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hcancel]
  rw [← Functor.map_comp_assoc]
  change (tensorPullback g).map
      (I.toRightDerivedZero' (pushforward f) ≫ K.homologyπ 0) ≫
        ((K.sc 0).mapHomologyIso (tensorPullback g)).inv ≫
          HomologicalComplex.homologyMap (flatBaseChangeResolutionC f g I J t) 0 ≫
            (J.isoRightDerivedObj (pushforward (pullback.fst g f)) 0).inv =
    β ≫ J.toRightDerivedZero' (pushforward (pullback.fst g f)) ≫ K'.homologyπ 0 ≫
      (J.isoRightDerivedObj (pushforward (pullback.fst g f)) 0).inv
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (J.isoRightDerivedObj (pushforward (pullback.fst g f)) 0).inv) hh

end AlgebraicGeometry.Scheme.Modules
