/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-!
# Support and pullback of finite type quasi-coherent modules

Source: Stacks Project, Morphisms of Schemes, Lemma 056J (lemma-support-finite-type)
(blueprint: lem-weil-pbc-support-pullback-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open TopologicalSpace in
/-- Restriction preserves finite type: pull the local generating cover back along
`Over.forget U`; its local maps preserve colimits and the unit, hence carry each finite
family of generators to a finite family. Source: Stacks Project, Modules, Tag 01B5,
the locality of finite type. This generalizes the scheme-only private helper in
`WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent` to arbitrary
ring sheaves on spaces. -/
private theorem finiteType_over_ringSheaf (T : Type u) [TopologicalSpace T]
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (F : SheafOfModules.{u} R)
    [F.IsFiniteType] (U : TopologicalSpace.Opens T) : (F.over U).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let G := Over.forget U
  let J := Opens.grothendieckTopology T
  let K := J.over U
  let S := R.over U
  let φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R := 𝟙 _
  let d : (F.over U).LocalGeneratorsData :=
    { I := Σ (V : Over U) (i : q.I), G.obj V ⟶ q.X i
      X := fun i ↦ i.1
      coversTop := fun V ↦ by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj V)))
        intro W g ⟨i, ⟨v⟩⟩
        exact ⟨⟨W, i, v⟩, ⟨𝟙 _⟩⟩
      generators := fun i ↦ by
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        have : G'.IsContinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          Functor.isContinuous_comp _ _ _ (J.over _) _
        have : G'.IsCocontinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          isCocontinuous_comp _ _ _ (J.over _)
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (q.X i.2.1))).obj (R.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          SheafOfModules.isLeftAdjoint_pushforward_of_isIso.{u} ψ
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) (Iso.refl _) }
  apply SheafOfModules.IsFiniteType.mk (R := R.over U)
  refine ⟨d, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.1
  dsimp only [d]
  infer_instance

open TopologicalSpace in
private theorem finite_stalk_from_affine {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hfinite : Module.Finite Γ(X, U) Γ(F, U) :=
    (((quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1 U hU).1.mp
      (finiteType_over_ringSheaf X X.ringCatSheaf F U)
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(X, U)) (M := Γ(F, U))
  let g := F.presheaf.germ U x hx
  let N := Submodule.span (X.presheaf.stalk x) (Set.range (fun i ↦ g (v i)))
  have hg (m : Γ(F, U)) : g m ∈ N := by
    have hm : m ∈ Submodule.span Γ(X, U) (Set.range v) := by rw [hv]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
        obtain ⟨i, rfl⟩ := hm
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simp [g]
    | add a b _ _ ha hb => simpa [g] using N.add_mem ha hb
    | smul r m _ hm =>
        simpa only [g, germ_smul] using N.smul_mem (X.presheaf.germ U x hx r) hm
  have he := (finite_type_module_support_closed X F).1 ⟨U, hU⟩ x hx
  obtain ⟨e, he⟩ := he
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hN : N = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨w, rfl⟩ := e.surjective z
    induction w using LocalizedModule.induction_on with
    | h m t =>
        have ht : IsUnit (X.presheaf.germ U x hx t.1) :=
          IsLocalization.map_units (X.presheaf.stalk x) t
        apply (N.smul_mem_iff_of_isUnit ht).mp
        rw [he m t]
        exact hg m
  constructor
  rw [← hN]
  exact Submodule.fg_span (Set.finite_range (fun i ↦ g (v i)))

private theorem subsingleton_extendScalars_field {K L : Type u} [Field K] [Field L]
    (f : K →+* L) (M : ModuleCat K) :
    Subsingleton ((ModuleCat.extendScalars f).obj M) ↔ Subsingleton M := by
  let := f.toAlgebra
  change Subsingleton (TensorProduct K L M) ↔ Subsingleton M
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right K L

private theorem residueFiber_pullback_subsingleton {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (y : Y) :
    Subsingleton (residueFiber ((tensorPullback f).obj F) y) ↔
      Subsingleton (residueFiber F (f y)) := by
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso f y
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace (f y)).obj F
  let a := (f.stalkMap y).hom
  let b := (Y.residue y).hom
  let c := (X.residue (f y)).hom
  let d := (f.residueFieldMap y).hom
  have h : b.comp a = d.comp c := by
    exact congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f y).symm
  let i₁ := (ModuleCat.extendScalars b).mapIso (e.app F)
  let i₂ := ((ModuleCat.extendScalarsComp a b).app M).symm
  let i₃ := (ModuleCat.extendScalarsComp c d).app M
  have h₁ : Subsingleton (residueFiber ((tensorPullback f).obj F) y) ↔
      Subsingleton ((ModuleCat.extendScalars (b.comp a)).obj M) :=
    (i₁ ≪≫ i₂).toLinearEquiv.toEquiv.subsingleton_congr
  rw [h₁, h]
  exact i₃.toLinearEquiv.toEquiv.subsingleton_congr.trans
    (subsingleton_extendScalars_field d (residueFiber F (f y)))

/-- The support of a finite type quasi-coherent module is closed, is detected by its
residue-field fibres, and pulls back to the inverse image under every scheme morphism.
Support is the inline nonzero-stalk locus of def-weil-pbc-closed-subset-proper-over-base;
membership in it is nonvanishing of the stalk by definition, so part (2) is stated as the
Nakayama equivalence with the residue fibre `residueFiber F x` (κ(x) ⊗ F_x).
Source: Stacks Project, Morphisms of Schemes, Lemma 056J (lemma-support-finite-type).
(blueprint: lem-weil-pbc-support-pullback-finite-type)

Proof:
1. Apply lem-weil-pbc-finite-type-module-support-closed to obtain closedness.
2. Membership in support is nonvanishing of the stalk by
   def-weil-pbc-closed-subset-proper-over-base.
3. Choose an affine neighbourhood of x (def-pc-scheme). By the affine description in
   lem-weil-pbc-finite-type-module-support-closed, its finite module localizes to F_x.
   The images of a finite generating family generate this localization, hence F_x is finite.
4. The stalk ring is local and its residue field is def-weil-residue-field. Apply
   lem-weil-pbc-nakayama-local-generators to the empty family: F_x vanishes precisely
   when its tensor product with the residue field vanishes. This proves both equivalences.
5. The pullback is finite type by lem-weil-pbc-module-pullback-finite-type. Its stalk is
   finite by lem-weil-pbc-module-stalk-pullback, Module.Finite.base_change, and the
   stalk isomorphism, so no quasi-coherence result for the pullback is needed.
6. For y mapping to x, extend the stalk isomorphism along the residue map. The identity
   between the two composites of stalk and residue-field maps is
   Scheme.residue_residueFieldMap. ModuleCat.extendScalarsComp identifies the pullback
   residue fibre with scalar extension of the original residue fibre along the induced
   field map.
7. Scalar extension along a field extension reflects subsingleton modules by
   Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right.
8. Apply the residue-fibre equivalence from step 4 to both finite stalks and use the
   comparison in steps 6--7. Set extensionality gives the asserted inverse-image equality. -/
theorem finiteType_module_support_pullback {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ x : X, ¬ Subsingleton (F.presheaf.stalk x) ↔ ¬ Subsingleton (residueFiber F x)) ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
        ((tensorPullback f).obj F).IsFiniteType ∧
          {y : Y | ¬ Subsingleton (((tensorPullback f).obj F).presheaf.stalk y)} =
            f.base ⁻¹' {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  have hres {Z : Scheme.{u}} (G : Z.Modules) (z : Z)
      [Module.Finite (Z.presheaf.stalk z) (G.presheaf.stalk z)] :
      ¬ Subsingleton (G.presheaf.stalk z) ↔ ¬ Subsingleton (residueFiber G z) := by
    let := (Z.residue z).hom.toAlgebra
    change ¬ Subsingleton (G.presheaf.stalk z) ↔
      ¬ Subsingleton (TensorProduct (Z.presheaf.stalk z) (Z.residueField z)
        (G.presheaf.stalk z))
    exact (not_congr IsLocalRing.subsingleton_tensorProduct).symm
  have (x : X) := finite_stalk_from_affine F x
  refine ⟨(finite_type_module_support_closed X F).2.2.2, (fun x ↦ hres F x), ?_⟩
  intro Y f
  have hfinite := (tensorPullback_isFiniteType Y X f F).1
  refine ⟨hfinite, ?_⟩
  ext y
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso f y
  let := (f.stalkMap y).hom.toAlgebra
  have hbase : Module.Finite (Y.presheaf.stalk y)
      ((ModuleCat.extendScalars (f.stalkMap y).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (f y)).obj F)) :=
    inferInstanceAs (Module.Finite (Y.presheaf.stalk y)
      (TensorProduct (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
        (F.presheaf.stalk (f y))))
  have hbase' : Module.Finite (Y.presheaf.stalk y)
      ((X.toRingedSpace.moduleStalkFunctor (f y) ⋙
        ModuleCat.extendScalars (f.stalkMap y).hom).obj F) := hbase
  have hfiniteStalk : Module.Finite (Y.presheaf.stalk y)
      (((tensorPullback f).obj F).presheaf.stalk y) :=
    Module.Finite.of_surjective (e.app F).symm.toLinearEquiv.toLinearMap
      (e.app F).symm.toLinearEquiv.surjective
  change ¬ Subsingleton (((tensorPullback f).obj F).presheaf.stalk y) ↔
    ¬ Subsingleton (F.presheaf.stalk (f y))
  exact (hres _ y).trans
    ((not_congr (residueFiber_pullback_subsingleton f F y)).trans (hres F (f y)).symm)

end AlgebraicGeometry.Scheme.Modules
