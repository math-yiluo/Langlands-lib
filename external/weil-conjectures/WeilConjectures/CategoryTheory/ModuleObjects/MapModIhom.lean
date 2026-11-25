/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom

/-!

# Transport of module objects commutes with internal homs

Let `C` and `D` be closed symmetric monoidal Grothendieck abelian categories, `R : C` a
commutative algebra object, and `F : C ⥤ D` a braided strong monoidal functor which is exact
(it preserves finite limits and coequalizers) and commutes with internal homs: the comparison
maps `F [Z, Y] ⟶ [F Z, F Y]` (`Functor.LaxMonoidal.ihomComparison`) are isomorphisms. Then the
transport `F.mapMod R : Mod C R ⥤ Mod D (F R)` of module objects, which is strong monoidal for the
relative tensor products (`Functor.monoidal_mapMod`), also commutes with the internal homs of
module objects (`Mod.monoidalClosed`): the comparison maps
`F Hom_R(M, N) ⟶ Hom_{F R}(F M, F N)` are isomorphisms (`Mod.isIso_ihomComparison_mapMod`).

## The argument

The internal hom `Hom_R(M, N)` of `Mod.monoidalClosed` is an abstract right adjoint. We show that
it is the equalizer of the two maps `[M, N] ⇉ [R ⊗ M, N]` of internal homs of `C`,
`f ↦ f ∘ act_M` and `f ↦ act_N ∘ (R ⊗ f)` (`Mod.isLimitIhomToHomMod`), through the map
`Mod.ihomToHomMod : Hom_R(M, N) ⟶ [M, N]` adjoint to the evaluation: a linear map
`P ⟶ [M, N]` equalizing the two maps is the same as an `R`-bilinear map `P ⊗ M ⟶ N`, that is a
map `P ⊗_R M ⟶ N` (`Mod.toHomMod`, `Mod.ofHomMod`). The functor `F` preserves this equalizer,
and carries the two maps to the corresponding maps for `F M` and `F N` up to the comparison
isomorphisms of `F` (`Mod.map_pre_act_comp_ihomComparison`,
`Mod.map_homModB_comp_ihomComparison`); and the comparison map of `F.mapMod R` is compatible with
the two equalizer maps (`Mod.ihomComparison_mapMod_app_hom_comp`).

-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj MonoidalClosed Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-! ### The internal hom of module objects as an equalizer -/

/-- For a linear map `f : P ⊗_R M ⟶ N`, the composite `P ⊗ M ⟶ P ⊗_R M ⟶ N` is linear in
`P`. -/
lemma tensorObjπ_comp_linear {P M N : Mod C R} (f : P ⊗ M ⟶ N) :
    (α_ R P.X M.X).inv ≫ act P.X ▷ M.X ≫ tensorObjπ P M ≫ f.hom =
      R ◁ (tensorObjπ P M ≫ f.hom) ≫ act N.X := by
  rw [MonoidalCategory.whiskerLeft_comp_assoc, ← act_hom f, whiskerLeft_tensorπ_smul_assoc]

/-- The linear map `P ⟶ [M, N]` adjoint to a linear map `P ⊗_R M ⟶ N`. -/
noncomputable def toHomMod {P M N : Mod C R} (f : P ⊗ M ⟶ N) : P ⟶ homMod R M.X N :=
  homMk (curry ((β_ M.X P.X).hom ≫ tensorObjπ P M ≫ f.hom))
    ((tensorRight_linear_iff P N M.X _).1 (tensorObjπ_comp_linear f))

lemma toHomMod_hom {P M N : Mod C R} (f : P ⊗ M ⟶ N) :
    (toHomMod f).hom = curry ((β_ M.X P.X).hom ≫ tensorObjπ P M ≫ f.hom) := rfl

/-- The map `P ⟶ [M, N]` adjoint to a linear map `P ⊗_R M ⟶ N` equalizes the two maps
`[M, N] ⇉ [R ⊗ M, N]`. -/
lemma toHomMod_condition {P M N : Mod C R} (f : P ⊗ M ⟶ N) :
    toHomMod f ≫ homModPre (act M.X) N = toHomMod f ≫ homModB R M N :=
  Mod.hom_ext _ _ ((coequalizes_iff P M N _ (tensorObjπ_comp_linear f)).1 (by
    rw [rightAct, tensorObjπ_condition_assoc, Iso.inv_hom_id_assoc]))

lemma toHomMod_comp {P' P M N : Mod C R} (g : P' ⟶ P) (f : P ⊗ M ⟶ N) :
    toHomMod (g ▷ M ≫ f) = g ≫ toHomMod f := by
  refine Mod.hom_ext _ _ ?_
  rw [comp_hom', toHomMod_hom, toHomMod_hom, ← curry_natural_left, comp_hom',
    tensorObjπ_whiskerRight_assoc, ← BraidedCategory.braiding_naturality_right_assoc]

lemma toHomMod_injective {P M N : Mod C R} {f f' : P ⊗ M ⟶ N}
    (h : toHomMod f = toHomMod f') : f = f' := by
  have h' := congrArg (fun g ↦ uncurry g.hom) h
  simp only [toHomMod_hom, uncurry_curry, cancel_epi] at h'
  exact Mod.hom_ext _ _ h'

/-- A linear map `P ⟶ [M, N]` equalizing the two maps `[M, N] ⇉ [R ⊗ M, N]`, that is an
`R`-bilinear map `P ⊗ M ⟶ N`, as a linear map `P ⊗_R M ⟶ N`. -/
noncomputable def ofHomMod {P M N : Mod C R} (v : P ⟶ homMod R M.X N)
    (hv : v ≫ homModPre (act M.X) N = v ≫ homModB R M N) : P ⊗ M ⟶ N :=
  have hlin : (α_ R P.X M.X).inv ≫ act P.X ▷ M.X ≫ ((β_ M.X P.X).inv ≫ uncurry v.hom) =
      R ◁ ((β_ M.X P.X).inv ≫ uncurry v.hom) ≫ act N.X :=
    (tensorRight_linear_iff P N M.X _).2 (by
      rw [Iso.hom_inv_id_assoc, curry_uncurry]
      exact act_hom v)
  have hbal := (coequalizes_iff P M N _ hlin).2 (by
    rw [Iso.hom_inv_id_assoc, curry_uncurry]
    exact congrArg Mod.Hom.hom hv)
  homMk (tensorObjDesc P M ((β_ M.X P.X).inv ≫ uncurry v.hom) (by
      rw [rightAct] at hbal
      rw [Category.assoc, hbal, Iso.hom_inv_id_assoc])) (by
    rw [← cancel_epi (R ◁ tensorObjπ P M), whiskerLeft_tensorπ_smul_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorObjπ_tensorObjDesc]
    exact hlin)

lemma tensorObjπ_ofHomMod_hom {P M N : Mod C R} (v : P ⟶ homMod R M.X N)
    (hv : v ≫ homModPre (act M.X) N = v ≫ homModB R M N) :
    tensorObjπ P M ≫ (ofHomMod v hv).hom = (β_ M.X P.X).inv ≫ uncurry v.hom :=
  tensorObjπ_tensorObjDesc _ _ _ _

lemma toHomMod_ofHomMod {P M N : Mod C R} (v : P ⟶ homMod R M.X N)
    (hv : v ≫ homModPre (act M.X) N = v ≫ homModB R M N) :
    toHomMod (ofHomMod v hv) = v := by
  refine Mod.hom_ext _ _ ?_
  rw [toHomMod_hom, tensorObjπ_ofHomMod_hom, Iso.hom_inv_id_assoc, curry_uncurry]

/-- The evaluation `Hom_R(M, N) ⊗_R M ⟶ N`. -/
noncomputable def ihomEvRight (M N : Mod C R) : (CategoryTheory.ihom M).obj N ⊗ M ⟶ N :=
  (β_ _ M).hom ≫ (CategoryTheory.ihom.ev M).app N

/-- The internal hom `Hom_R(M, N)` of `R`-modules maps to the internal hom `[M, N]` of the
underlying objects: the map adjoint to the evaluation. -/
noncomputable def ihomToHomMod (M N : Mod C R) :
    (CategoryTheory.ihom M).obj N ⟶ homMod R M.X N :=
  toHomMod (ihomEvRight M N)

lemma whiskerRight_ihomEvRight {P M N : Mod C R} (g : P ⟶ (CategoryTheory.ihom M).obj N) :
    g ▷ M ≫ ihomEvRight M N = (β_ P M).hom ≫ uncurry g := by
  rw [ihomEvRight, BraidedCategory.braiding_naturality_left_assoc, uncurry_eq]

lemma ihomToHomMod_condition (M N : Mod C R) :
    ihomToHomMod M N ≫ homModPre (act M.X) N = ihomToHomMod M N ≫ homModB R M N :=
  toHomMod_condition _

/-- **The internal hom of `R`-modules is the equalizer of `[M, N] ⇉ [R ⊗ M, N]`**, the maps
being `f ↦ f ∘ act_M` and `f ↦ act_N ∘ (R ⊗ f)`. -/
noncomputable def isLimitIhomToHomMod (M N : Mod C R) :
    IsLimit (Fork.ofι (ihomToHomMod M N) (ihomToHomMod_condition M N) :
      Fork (homModPre (act M.X) N) (homModB R M N)) :=
  Fork.IsLimit.mk _ (fun s ↦ curry ((β_ s.pt M).inv ≫ ofHomMod s.ι s.condition))
    (fun s ↦ by
      dsimp only [Fork.ofι_pt, Fork.ι_ofι]
      rw [ihomToHomMod, ← toHomMod_comp, whiskerRight_ihomEvRight, uncurry_curry,
        Iso.hom_inv_id_assoc, toHomMod_ofHomMod])
    (fun s m hm ↦ by
      dsimp only [Fork.ofι_pt, Fork.ι_ofι] at hm ⊢
      rw [eq_curry_iff, Iso.eq_inv_comp, ← whiskerRight_ihomEvRight]
      refine toHomMod_injective ?_
      rw [toHomMod_comp, toHomMod_ofHomMod]
      exact hm)

/-- The underlying map `Hom_R(M, N) ⟶ [M, N]` is adjoint to the evaluation
`M ⊗ Hom_R(M, N) ⟶ M ⊗_R Hom_R(M, N) ⟶ N`. -/
lemma uncurry_ihomToHomMod_hom (M N : Mod C R) :
    uncurry (ihomToHomMod M N).hom =
      tensorObjπ M ((CategoryTheory.ihom M).obj N) ≫ ((CategoryTheory.ihom.ev M).app N).hom := by
  rw [ihomToHomMod, toHomMod_hom, uncurry_curry, ihomEvRight, comp_hom', braiding_hom_hom,
    tensorObjπ_braidingHomX_assoc, SymmetricCategory.symmetry_assoc]

/-! ### Transport along an exact functor commuting with internal homs -/

section Functor

variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]

open Functor.LaxMonoidal

open scoped Obj

/-- The comparison map `F Hom_R(M, N) ⟶ Hom_{F R}(F M, F N)` of `F.mapMod R` is compatible with
the maps to the internal homs `[F M, F N]` of the underlying objects. -/
lemma ihomComparison_mapMod_app_hom_comp (M N : Mod C R) :
    ((ihomComparison (F.mapMod R) M).app N).hom ≫
        (ihomToHomMod ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom =
      F.map (ihomToHomMod M N).hom ≫ (ihomComparison F M.X).app N.X := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_ihomToHomMod_hom, uncurry_eq,
    MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← tensorObjπ_whiskerLeft_assoc]
  rw [← comp_hom']
  erw [ihomComparison_ev]
  rw [comp_hom', Functor.mapMod_μ_hom]
  erw [ihomComparison_ev, μ_natural_right_assoc]
  rw [← F.map_comp, ← uncurry_eq, uncurry_ihomToHomMod_hom, F.map_comp]
  erw [Mod.tensorObjπ_tensorObjDesc_assoc]
  rw [Category.assoc]
  rfl

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [IsCommMonObj R] [Abelian D]
  [IsGrothendieckAbelian.{v'} D]
  [PreservesColimitsOfShape WalkingParallelPair F] in
/-- The comparison maps of `F` intertwine the maps `f ↦ f ∘ act_M` for `M` and for `F M`. -/
lemma map_pre_act_comp_ihomComparison (M N : Mod C R) :
    F.map ((pre (act M.X)).app N.X) ≫ (ihomComparison F (R ⊗ M.X)).app N.X ≫
        (pre (Functor.LaxMonoidal.μ F R M.X)).app (F.obj N.X) =
      (ihomComparison F M.X).app N.X ≫
        (pre (act ((F.mapMod R).obj M).X)).app (F.obj N.X) := by
  rw [map_pre_app_comp_ihomComparison_assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [Abelian D]
  [IsGrothendieckAbelian.{v'} D]
  [PreservesColimitsOfShape WalkingParallelPair F] in
/-- The comparison maps of `F` intertwine the maps `f ↦ act_N ∘ (R ⊗ f)` for `M`, `N` and for
`F M`, `F N`. -/
lemma map_homModB_comp_ihomComparison (M N : Mod C R) :
    F.map (homModB R M N).hom ≫ (ihomComparison F (R ⊗ M.X)).app N.X ≫
        (pre (Functor.LaxMonoidal.μ F R M.X)).app (F.obj N.X) =
      (ihomComparison F M.X).app N.X ≫
        (homModB (F.obj R) ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom := by
  change F.map (curry ((α_ R M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
        R ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X)) ≫
      (ihomComparison F (R ⊗ M.X)).app N.X ≫
      (pre (Functor.LaxMonoidal.μ F R M.X)).app (F.obj N.X) =
    (ihomComparison F M.X).app N.X ≫
      curry ((α_ (F.obj R) (F.obj M.X) ((CategoryTheory.ihom (F.obj M.X)).obj (F.obj N.X))).hom ≫
        F.obj R ◁ (CategoryTheory.ihom.ev (F.obj M.X)).app (F.obj N.X) ≫
          Functor.LaxMonoidal.μ F R N.X ≫ F.map (act N.X))
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, uncurry_natural_left, uncurry_eq]
  erw [ihomComparison_ev]
  rw [μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq, uncurry_curry, uncurry_natural_left,
    uncurry_curry]
  erw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ihomComparison_ev]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [μ_natural_right_assoc]
  rw [associativity_assoc]

variable [PreservesFiniteLimits F] [∀ Z : C, IsIso (ihomComparison F Z)]

/-- **Transport of module objects along an exact braided functor commuting with internal homs
commutes with internal homs**: the comparison `F Hom_R(M, N) ⟶ Hom_{F R}(F M, F N)` is an
isomorphism. Both sides are equalizers of `[M, N] ⇉ [R ⊗ M, N]` (`Mod.isLimitIhomToHomMod`),
respectively of its image under `F`, which `F` preserves. -/
instance isIso_ihomComparison_mapMod (M : Mod C R) :
    IsIso (ihomComparison (F.mapMod R) M) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  let c := (ihomComparison (F.mapMod R) M).app N
  suffices IsIso ((forget _).map c) from isIso_of_reflects_iso c (forget _)
  have hC := isLimitForkMapOfIsLimit (forget R) _ (isLimitIhomToHomMod M N)
  have hFC := isLimitForkMapOfIsLimit F _ hC
  have hD := isLimitForkMapOfIsLimit (forget (F.obj R)) _
    (isLimitIhomToHomMod ((F.mapMod R).obj M) ((F.mapMod R).obj N))
  have hm₁ : Mono (F.map (ihomToHomMod M N).hom) := Fork.IsLimit.mono hFC
  have hm₂ : Mono (ihomToHomMod ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom :=
    Fork.IsLimit.mono hD
  let u := (ihomComparison F M.X).app N.X
  let v := (ihomComparison F (R ⊗ M.X)).app N.X ≫
    (pre (Functor.LaxMonoidal.μ F R M.X)).app (F.obj N.X)
  have ha := map_pre_act_comp_ihomComparison F M N
  have hb := map_homModB_comp_ihomComparison F M N
  have hc := ihomComparison_mapMod_app_hom_comp F M N
  obtain ⟨d, hd⟩ := Fork.IsLimit.lift' hFC
    ((ihomToHomMod ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom ≫ inv u) (by
      rw [← cancel_mono v]
      simp only [Category.assoc, v]
      erw [ha, hb]
      rw [IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
      exact congrArg Hom.hom (ihomToHomMod_condition _ _))
  rw [Fork.ι_ofι] at hd
  refine ⟨d, ?_, ?_⟩
  · rw [← cancel_mono (F.map (ihomToHomMod M N).hom), Category.assoc]
    erw [hd, reassoc_of% hc]
    rw [IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (ihomToHomMod ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom,
      Category.assoc]
    erw [hc, reassoc_of% hd]
    rw [IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

end Functor

end CategoryTheory.Mod
