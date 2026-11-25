/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import all WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality

/-! # Shrinking equality of morphisms with finite locally free source

Source: Stacks Project, Tag 05GF, Lemma 10.79.2, finite relations argument.
(blueprint: lem-sc-finite-locally-free-stalk-hom-equality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_shrink_of_stalk_eq
    {X : Scheme.{u}} (M N : X.Modules) [M.IsFiniteLocallyFree] (x : X)
    (f g : M ⟶ N)
    (h : (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u} x).map f =
      (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u} x).map g) :
    ∃ (V : X.Opens), x ∈ V ∧
      (restrictFunctor V.ι).map f = (restrictFunctor V.ι).map g:= by
  classical
  obtain ⟨C, I, hI, hxC, ⟨e₀⟩⟩ := exists_restrict_iso_free_of_isFiniteLocallyFree M x
  let : Finite I := hI
  let y : C.toScheme := ⟨x, hxC⟩
  let R := restrictFunctor C.ι
  let F := toPresheaf C.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y
  have hc : F.map (R.map f) = F.map (R.map g) :=
    map_eq_of_iso (restrictStalkNatIso C.ι y).symm h
  let f' := e₀.inv ≫ R.map f
  let g' := e₀.inv ≫ R.map g
  have hs : F.map f' = F.map g' := by
    simp only [f', g', Functor.map_comp, hc]
  have hg (i : I) :
      (R.obj N).presheaf.germ ⊤ y (by trivial)
          (Hom.app (SheafOfModules.ιFree i ≫ f') ⊤ (1 : Γ(C.toScheme, ⊤))) =
        (R.obj N).presheaf.germ ⊤ y (by trivial)
          (Hom.app (SheafOfModules.ιFree i ≫ g') ⊤ (1 : Γ(C.toScheme, ⊤))) := by
    have hh := congrArg (fun t ↦ F.map (SheafOfModules.ιFree i) ≫ t) hs
    rw [← Functor.map_comp, ← Functor.map_comp] at hh
    have ht := ConcreteCategory.congr_hom hh
      (TopCat.Presheaf.germ (X := C.toScheme.toTopCat)
        (SheafOfModules.unit C.toScheme.ringCatSheaf).val.presheaf ⊤ y (by trivial)
        (1 : Γ(C.toScheme, ⊤)))
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (Hom.mapPresheaf (SheafOfModules.ιFree i ≫ f')) _).symm.trans
      (ht.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
        (Hom.mapPresheaf (SheafOfModules.ιFree i ≫ g')) _))
  obtain ⟨V', _, hyV', heq⟩ := exists_restrict_eq_of_free_germs_eq y f' g' hg ⊤ (by trivial)
  have heq' : (restrictFunctor V'.ι).map (R.map f) =
      (restrictFunctor V'.ι).map (R.map g) := by
    apply (cancel_epi ((restrictFunctor V'.ι).map e₀.inv)).mp
    exact ((restrictFunctor V'.ι).map_comp _ _).symm.trans
      (heq.trans ((restrictFunctor V'.ι).map_comp _ _))
  let V := C.ι ''ᵁ V'
  have hxV : x ∈ V := ⟨y, hyV', rfl⟩
  let j := C.ι.isoImage V'
  have hj : j.hom ≫ V.ι = V'.ι ≫ C.ι := C.ι.isoImage_hom_ι V'
  refine ⟨V, hxV, ?_⟩
  apply restrict_map_injective_of_isIso j.hom
  let d := restrictFunctorCongr hj ≪≫ restrictFunctorComp V'.ι C.ι
  let e := (restrictFunctorComp j.hom V.ι).symm ≪≫ d
  exact map_eq_of_iso e.symm heq'

/-- Equality on germs of local sections gives equality on a smaller neighbourhood.
Source: Stacks Project, Tag 05GF, Lemma 10.79.2.
(blueprint: lem-sc-finite-locally-free-stalk-hom-equality)

Proof: Intersect U with a finite free frame neighbourhood for M at x. Apply the
given equality of germs to the finitely many frame sections on this intersection.
For each basis vector the germ equality criterion supplies a smaller open where
its two images agree. Intersect these finitely many opens. The restricted maps
agree on every basis vector, so the free universal property makes them equal.
The restriction composition isomorphism identifies these maps with direct
restriction from U to the final open. For rank zero the source is zero and
there are no equations to shrink. No finiteness condition on N is needed. -/
theorem exists_shrink_restrict_hom_eq_of_germs
    {W : Scheme.{u}} (M N : W.Modules) [M.IsFiniteLocallyFree]
    (x : W) (U : W.Opens) (hxU : x ∈ U)
    (f g : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N)
    (h : ∀ (V : U.toScheme.Opens) (hxV : (⟨x, hxU⟩ : U.toScheme) ∈ V)
      (m : Γ((restrictFunctor U.ι).obj M, V)),
      N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ (Hom.app f V m) =
        N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ (Hom.app g V m)) :
    ∃ (V : W.Opens) (_ : x ∈ V) (hVU : V ≤ U),
      (restrictFunctor (W.homOfLE hVU)).map f =
        (restrictFunctor (W.homOfLE hVU)).map g := by
  classical
  let R := restrictFunctor U.ι
  let y : U.toScheme := ⟨x, hxU⟩
  let F := toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y
  let d := restrictStalkNatIso U.ι y
  have : (R.obj M).IsFiniteLocallyFree := by
    exact SheafOfModules.IsFiniteLocallyFree.of_iso (R := U.toScheme.ringCatSheaf)
      ((restrictFunctorIsoPullback U.ι).symm.app M)
  have hs : F.map f = F.map g := by
    ext m
    obtain ⟨V, hyV, m, rfl⟩ := (R.obj M).presheaf.exists_germ_eq m
    apply (d.app N).addCommGroupIsoToAddEquiv.injective
    have hf := TopCat.Presheaf.stalkFunctor_map_germ_apply V y hyV (Hom.mapPresheaf f) m
    have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply V y hyV (Hom.mapPresheaf g) m
    have df := ConcreteCategory.congr_hom
      (germ_restrictStalkNatIso_hom_app U.ι y N hyV) (Hom.app f V m)
    have dg := ConcreteCategory.congr_hom
      (germ_restrictStalkNatIso_hom_app U.ι y N hyV) (Hom.app g V m)
    exact (congrArg (fun a ↦ d.hom.app N a) hf).trans
      (df.trans ((h V hyV m).trans (dg.symm.trans
        (congrArg (fun a ↦ d.hom.app N a) hg).symm)))
  obtain ⟨C, hyC, heq⟩ := exists_shrink_of_stalk_eq (R.obj M) (R.obj N) y f g hs
  let V := U.ι ''ᵁ C
  have hxV : x ∈ V := ⟨y, hyC, rfl⟩
  have hVU : V ≤ U := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact t.property
  let j := U.ι.isoImage C
  let a := W.homOfLE hVU
  have hj : j.hom ≫ a = C.ι := by
    apply (cancel_mono U.ι).mp
    simpa only [a, Category.assoc, Scheme.homOfLE_ι] using U.ι.isoImage_hom_ι C
  refine ⟨V, hxV, hVU, ?_⟩
  apply restrict_map_injective_of_isIso j.hom
  let e := (restrictFunctorComp j.hom a).symm ≪≫ restrictFunctorCongr hj
  exact map_eq_of_iso e.symm heq


end AlgebraicGeometry.Scheme.Modules
