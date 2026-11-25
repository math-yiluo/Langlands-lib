/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Equality of maps with finite free source near a stalk

Source: lemma-coherent-base-change-invertible-sheaves--3, finite germ calculation.
(blueprint: lem-pc-finite-free-stalk-map-eq-shrink)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_map_eq_of_pullback_eq
    {X Y : Scheme.{u}} (a : X ⟶ Y) (x : X) [IsIso (a.stalkMap x)]
    {M N : Y.Modules} (f g : M ⟶ N)
    (h : (pullback a).map f = (pullback a).map g) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace (a x)).map f =
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (a x)).map g := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction a)).leftAdjointUniq
    (pullbackPushforwardAdjunction a)
  have ht : (tensorPullback a).map f = (tensorPullback a).map g := by
    apply (cancel_mono (e.hom.app N)).1
    rw [e.hom.naturality, e.hom.naturality, h]
  obtain ⟨d, _⟩ := exists_tensorPullback_stalk_iso a x
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace (a x)
  let E := ModuleCat.extendScalars (a.stalkMap x).hom
  let R := ModuleCat.restrictScalars (a.stalkMap x).hom
  have he : E.map (S.map f) = E.map (S.map g) := by
    apply (cancel_epi (d.hom.app M)).1
    calc
      _ = (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
          ((tensorPullback a).map f) ≫ d.hom.app N := (d.hom.naturality f).symm
      _ = (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
          ((tensorPullback a).map g) ≫ d.hom.app N := by rw [ht]
      _ = _ := d.hom.naturality g
  have : R.IsEquivalence := by
    let e := (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv
    change (ModuleCat.restrictScalars e.toRingHom).IsEquivalence
    infer_instance
  let adj := ModuleCat.extendRestrictScalarsAdj (a.stalkMap x).hom
  apply (cancel_mono (adj.unit.app (S.obj N))).1
  calc
    _ = adj.unit.app (S.obj M) ≫ R.map (E.map (S.map f)) :=
      adj.unit_naturality (S.map f)
    _ = adj.unit.app (S.obj M) ≫ R.map (E.map (S.map g)) := by rw [he]
    _ = _ := (adj.unit_naturality (S.map g)).symm

private theorem unit_hom_ext_top {X : Scheme.{u}} {N : X.Modules}
    (f g : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (h : Hom.app f ⊤ (1 : Γ(X, ⊤)) = Hom.app g ⊤ (1 : Γ(X, ⊤))) : f = g := by
  apply N.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  let i : U.unop ⟶ (⊤ : X.Opens) := homOfLE le_top
  calc
    _ = N.val.map i.op ((N.unitHomEquiv f).val (Opposite.op ⊤)) :=
      ((N.unitHomEquiv f).property i.op).symm
    _ = N.val.map i.op ((N.unitHomEquiv g).val (Opposite.op ⊤)) := congrArg _ h
    _ = _ := (N.unitHomEquiv g).property i.op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_restrict_eq_of_free_germs_eq
    {X : Scheme.{u}} {I : Type u} [Finite I] (x : X)
    {N : X.Modules} (f g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ N)
    (h : ∀ i : I,
      N.presheaf.germ ⊤ x (by trivial) (Hom.app (SheafOfModules.ιFree i ≫ f) ⊤ (1 : Γ(X, ⊤))) =
      N.presheaf.germ ⊤ x (by trivial) (Hom.app (SheafOfModules.ιFree i ≫ g) ⊤ (1 : Γ(X, ⊤))))
    (U : X.Opens) (hxU : x ∈ U) :
    ∃ (W : X.Opens) (_hWU : W ≤ U), x ∈ W ∧
      (restrictFunctor W.ι).map f = (restrictFunctor W.ι).map g := by
  classical
  have hi (i : I) := N.presheaf.germ_eq x (by trivial) (by trivial) _ _ (h i)
  choose V hxV a b he using hi
  let W : X.Opens := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le _ i)
  have hxW : x ∈ W := ⟨hxU, by
    change x ∈ (↑(⨅ i, V i) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV⟩
  refine ⟨W, hWU, hxW, ?_⟩
  apply (isColimitOfPreserves (restrictFunctor W.ι)
    (SheafOfModules.isColimitFreeCofan I)).hom_ext
  intro i
  change (restrictFunctor W.ι).map (SheafOfModules.ιFree i.as) ≫
      (restrictFunctor W.ι).map f =
    (restrictFunctor W.ι).map (SheafOfModules.ιFree i.as) ≫
      (restrictFunctor W.ι).map g
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply (cancel_epi (restrictUnitIso W.ι).inv).1
  apply unit_hom_ext_top
  change Hom.app (SheafOfModules.ιFree i.as ≫ f) (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv 1) =
    Hom.app (SheafOfModules.ιFree i.as ≫ g) (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv 1)
  simp only [map_one]
  have hi := congrArg (N.presheaf.map (homOfLE (hWV i.as)).op) (he i.as)
  have hmaps (c : V i.as ⟶ (⊤ : X.Opens)) (s : Γ(N, ⊤)) :
      N.presheaf.map (homOfLE (hWV i.as)).op (N.presheaf.map c.op s) =
        N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  simp only [hmaps] at hi
  have htop : W.ι ''ᵁ ⊤ = W := by simp
  rw [htop]
  have hn (t : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
      N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (Hom.app t ⊤ (1 : Γ(X, ⊤))) =
        Hom.app t W (1 : Γ(X, W)) := by
    exact (N.unitHomEquiv t).property (homOfLE (show W ≤ ⊤ from le_top)).op
  simpa only [hn] using hi

private theorem map_eq_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} {f g : M ⟶ N}
    (h : F.map f = F.map g) : G.map f = G.map g := by
  apply (cancel_epi (e.hom.app M)).1
  calc
    _ = F.map f ≫ e.hom.app N := (e.hom.naturality f).symm
    _ = F.map g ≫ e.hom.app N := by rw [h]
    _ = _ := e.hom.naturality g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrict_map_injective_of_isIso {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsIso a] {M N : Y.Modules} {f g : M ⟶ N}
    (h : (restrictFunctor a).map f = (restrictFunctor a).map g) : f = g := by
  apply hom_ext
  intro Q
  have hh := congrArg (fun t ↦ Hom.app t (a ⁻¹ᵁ Q)) h
  change Hom.app f (a ''ᵁ (a ⁻¹ᵁ Q)) = Hom.app g (a ''ᵁ (a ⁻¹ᵁ Q)) at hh
  have hQ : a ''ᵁ (a ⁻¹ᵁ Q) = Q := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  exact (congrArg (fun T ↦ Hom.app f T = Hom.app g T) hQ).mp hh

/-- Equality after pullback to the local scheme spreads for maps with finite free source.

Source: blueprint sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus,
finite germ calculation. (blueprint: lem-pc-finite-free-stalk-map-eq-shrink)

Proof: Use the given source isomorphism to obtain r generating sections over V.
The pullback equality implies equality of the germs of their images in N at y:
the stalk at the closed point of Spec O_{Y,y} of the pullback is canonically N_y.
For each generator the presheaf germ equality criterion gives an open neighbourhood
of y inside V on which its two images agree. Intersect these finitely many opens
with U. On that intersection the two maps agree on every generator, hence on the
whole restricted free source, and therefore on M. For r=0 there are no generators,
the source is zero, and W=U works. No finite generation of N is needed. -/
theorem exists_restrict_eq_of_pullback_eq
    {Y : Scheme.{u}} (r : ℕ) (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (M N : V.toScheme.Modules)
    (hM : Nonempty (M ≅ (restrictFunctor V.ι).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))
    (f g : M ⟶ N)
    (hfg : (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map f =
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map g)
    (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      (restrictFunctor (Y.homOfLE (hWU.trans hUV))).map f =
      (restrictFunctor (Y.homOfLE (hWU.trans hUV))).map g := by
  classical
  let x : V.toScheme := ⟨y, hyV⟩
  let a := V.fromSpecStalkOfMem y hyV
  let z := IsLocalRing.closedPoint (Y.presheaf.stalk y)
  have ha : IsIso (a.stalkMap z) := by
    dsimp [a, Scheme.Opens.fromSpecStalkOfMem]
    rw [Scheme.Hom.stalkMap_comp]
    have : IsIso ((V.toScheme.fromSpecStalk x).stalkMap
        ((Spec.map (inv (V.ι.stalkMap x))) z)) :=
      (Scheme.fromSpecStalk_local_properties V.toScheme x).2.2.2.1 _
    infer_instance
  have hax : a z = x := by
    apply Subtype.ext
    change (a ≫ V.ι) z = y
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    exact Y.fromSpecStalk_closedPoint
  have hs := stalk_map_eq_of_pullback_eq a z f g hfg
  rw [hax] at hs
  obtain ⟨eM⟩ := hM
  let e := eM ≪≫ restrictFreeIso V.ι (ULift.{u} (Fin r))
  let f' := e.inv ≫ f
  let g' := e.inv ≫ g
  have hs' :
      (RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace x).map f' =
        (RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace x).map g' := by
    simp only [f', g', Functor.map_comp, hs]
  have hg (i : ULift.{u} (Fin r)) :
      N.presheaf.germ ⊤ x (by trivial)
          (Hom.app (SheafOfModules.ιFree i ≫ f') ⊤ (1 : Γ(V.toScheme, ⊤))) =
        N.presheaf.germ ⊤ x (by trivial)
          (Hom.app (SheafOfModules.ιFree i ≫ g') ⊤ (1 : Γ(V.toScheme, ⊤))) := by
    have hh := congrArg (fun t ↦
      (RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace x).map
        (SheafOfModules.ιFree i) ≫ t) hs'
    rw [← Functor.map_comp, ← Functor.map_comp] at hh
    have ht := congrArg (fun t ↦ t
      (TopCat.Presheaf.germ (SheafOfModules.unit V.toScheme.ringCatSheaf).val.presheaf
        ⊤ x (by trivial) (1 : Γ(V.toScheme, ⊤)))) hh
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (Hom.mapPresheaf (SheafOfModules.ιFree i ≫ f')) _).symm.trans
      (ht.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
        (Hom.mapPresheaf (SheafOfModules.ιFree i ≫ g')) _))
  let U' : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have hxU' : x ∈ U' := hyU
  obtain ⟨W', hW'U', hxW', heq⟩ :=
    exists_restrict_eq_of_free_germs_eq x f' g' hg U' hxU'
  let W := V.ι ''ᵁ W'
  have hWU : W ≤ U := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact hW'U' hs
  have hyW : y ∈ W := ⟨x, hxW', rfl⟩
  refine ⟨W, hWU, hyW, ?_⟩
  have heq' : (restrictFunctor W'.ι).map f = (restrictFunctor W'.ι).map g := by
    apply (cancel_epi ((restrictFunctor W'.ι).map e.inv)).1
    simpa only [f', g', Functor.map_comp] using heq
  let j := V.ι.isoImage W'
  let d := Y.homOfLE (hWU.trans hUV)
  have hj : j.hom ≫ d = W'.ι := by
    apply (cancel_mono V.ι).1
    simpa only [d, Category.assoc, Scheme.homOfLE_ι] using V.ι.isoImage_hom_ι W'
  apply restrict_map_injective_of_isIso j.hom
  change (restrictFunctor d ⋙ restrictFunctor j.hom).map f =
    (restrictFunctor d ⋙ restrictFunctor j.hom).map g
  exact map_eq_of_iso
    (restrictFunctorCongr hj.symm ≪≫ restrictFunctorComp j.hom d) heq'

end AlgebraicGeometry.Scheme.Modules
