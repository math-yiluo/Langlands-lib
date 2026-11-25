/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

/-!
# Recovering constant modules from a constant underlying inverse image

Source: Stacks Project, Tag 0DV5 (2)--(3), Tag 0DV6, and sites-modules Tag 093S.
(blueprint: lem-weil-pbc-module-constant-of-set-pullback)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Embed the set into its free abelian group. Connected abelian constant sections
-- are constant; a local representative shows that this constant lies in the set.
private theorem set_constant_sections_bijective (X : Scheme.{u}) [ConnectedSpace X]
    (E : Type (u + 1)) :
    Function.Bijective
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj E)).app
        (Opposite.op (Etale.mk (𝟙 X)))) := by
  let A := AddCommGrpCat.of (FreeAbelianGroup E)
  let T := Etale.mk (𝟙 X)
  let S := (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj E
  let c := (sheafComposeNatIso X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).app
      ((Functor.const X.Etaleᵒᵖ).obj A)
  let i : E ⟶ (CategoryTheory.forget AddCommGrpCat.{u + 1}).obj A := ↾FreeAbelianGroup.of
  let j : S ⟶ (sheafForget X.smallEtaleTopology).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) :=
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).map i ≫ c.hom
  have hi : Mono i := (CategoryTheory.mono_iff_injective i).2 FreeAbelianGroup.of_injective
  have hconst : Mono ((Functor.const X.Etaleᵒᵖ).map i) :=
    (NatTrans.mono_iff_mono_app _).2 (fun _ ↦ hi)
  have hmap : Mono ((constantSheaf X.smallEtaleTopology (Type (u + 1))).map i) :=
    Functor.map_mono (presheafToSheaf X.smallEtaleTopology (Type (u + 1))) _
  have hj : Mono j := by
    dsimp [j]
    infer_instance
  have hjinj : Function.Injective (j.hom.app (Opposite.op T)) := by
    have : Mono ((sheafToPresheaf _ _).map j) := Functor.map_mono _ _
    exact (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app _).1 this (Opposite.op T))
  have hjunit (W : X.Etale) (e : E) :
      j.hom.app (Opposite.op W)
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj E)).app (Opposite.op W) e) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (Opposite.op W) (FreeAbelianGroup.of e) := by
    have hc := sheafComposeNatTrans_fac X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) (sheafificationAdjunction _ _)
      (sheafificationAdjunction _ _) ((Functor.const X.Etaleᵒᵖ).obj A)
    have hn := toSheafify_naturality (J := X.smallEtaleTopology)
      ((Functor.const X.Etaleᵒᵖ).map i)
    have hn' := congrArg (fun k ↦ k.app (Opposite.op W) e) hn
    have hc' := congrArg (fun k ↦ k.app (Opposite.op W) (FreeAbelianGroup.of e)) hc
    exact congrArg (fun z ↦ c.hom.hom.app (Opposite.op W) z) hn'.symm |>.trans hc'
  have hA := bijective_toSheafify_app_terminal X A
  constructor
  · intro e e' he
    apply FreeAbelianGroup.of_injective
    apply hA.injective
    exact (hjunit T e).symm.trans ((congrArg (j.hom.app (Opposite.op T)) he).trans (hjunit T e'))
  · intro σ
    obtain ⟨a, ha⟩ := hA.surjective (j.hom.app (Opposite.op T) σ)
    obtain ⟨x⟩ := ‹ConnectedSpace X›.toNonempty
    obtain ⟨W, g, w, ⟨e, he⟩, _⟩ := exists_of_mem_smallEtaleTopology (V := T)
      (Presheaf.imageSieve_mem X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj E)) σ) x
    have hW : (⊥ : Sieve W) ∉ X.smallEtaleTopology W := by
      intro hb
      obtain ⟨V, h, v, hh, _⟩ := exists_of_mem_smallEtaleTopology hb w
      exact hh
    have hinj := X.smallEtaleTopology.toSheafify_const_app_injective A hW
    have hrestrict := congrArg
      (fun z ↦ (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A).obj.map
        g.op) z) ha
    have hnat := NatTrans.naturality_apply j.hom g.op σ
    have hunitnat := NatTrans.naturality_apply
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)) g.op a
    have hae : a = FreeAbelianGroup.of e := by
      apply hinj
      exact hunitnat.trans (hrestrict.trans (hnat.symm.trans
        ((congrArg (j.hom.app (Opposite.op W)) he).symm.trans (hjunit W e))))
    refine ⟨e, hjinj ?_⟩
    rw [hjunit, ← hae]
    exact ha

/-- On a connected scheme, a module inverse image is constant when its underlying set
inverse image is constant. No finiteness or local constancy hypothesis is required.
Source: Stacks Project, Tag 0DV5 (2)--(3), Tag 0DV6, and sites-modules Tag 093S.
(blueprint: lem-weil-pbc-module-constant-of-set-pullback)

Proof: inverse image of module sheaves commutes with the underlying-set functor:
construct inverse image by sheafifying the filtered neighbourhood colimits, whose
module structures are the colimit module structures. The underlying-set functor
preserves these filtered colimits and sheafification. Thus the hypothesis makes the
underlying sheaf of the module inverse image constant. On a connected nonempty scheme,
global sections of a constant set sheaf are exactly its value: sections are locally
constant functions and hence constant. Consequently the constant-sheaf functor is
fully faithful and preserves finite products. Transport addition, zero, negation and
each scalar multiplication through the underlying constant-sheaf identification;
full faithfulness makes them operations on its value. Faithfulness gives the module
axioms. The identification then lifts to a module-sheaf isomorphism from the constant
sheaf of this module to the inverse image. Equivalently, the constant/global-sections
counit is an isomorphism after forgetting modules, hence is an isomorphism of module
sheaves. This also covers the zero module and arbitrary coefficient rings. -/
theorem module_pullback_isConstant_of_set_pullback
    {U X : Scheme.{u}} [ConnectedSpace X]
    (R : Type (u + 1)) [CommRing R] (f : X ⟶ U)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : ((etaleSetPullback f).obj
      ((sheafForget U.smallEtaleTopology).obj F)).IsConstant X.smallEtaleTopology) :
    ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj F).IsConstant
      X.smallEtaleTopology := by
  let T := Etale.mk (𝟙 X)
  let hT : CategoryTheory.Limits.IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let a := constantSheafAdj X.smallEtaleTopology (Type (u + 1)) hT
  have hunit (E : Type (u + 1)) : IsIso (a.unit.app E) := by
    change IsIso ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj E)).app (Opposite.op T))
    exact (CategoryTheory.isIso_iff_bijective _).2 (set_constant_sections_bijective X E)
  have : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
  have : (constantSheaf X.smallEtaleTopology (Type (u + 1))).Faithful :=
    a.fullyFaithfulLOfIsIsoUnit.faithful
  have : (constantSheaf X.smallEtaleTopology (Type (u + 1))).Full :=
    a.fullyFaithfulLOfIsIsoUnit.full
  obtain ⟨em⟩ := Etale.exists_upperStar_forget₂_natIso R f
  have hL : CategoryTheory.Limits.PreservesFiniteLimits (etaleSetPullback f) := by
    unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : CategoryTheory.AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      CategoryTheory.AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, _⟩ := etaleInverseImageAbelianLift_hom X U f hL
  let e : (sheafForget X.smallEtaleTopology).obj
      ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj F) ≅
      (etaleSetPullback f).obj ((sheafForget U.smallEtaleTopology).obj F) :=
    (sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).mapIso (em.app F) ≪≫
      ea.app ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj F)
  have := hF
  have hG := Sheaf.isConstant_congr X.smallEtaleTopology e.symm
  let G := (Etale.upperStar (ModuleCat.{u + 1} R) f).obj F
  -- Only the set constant functor must be fully faithful: reflect the module counit.
  have hforget : IsIso ((sheafForget X.smallEtaleTopology).map
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) hT).counit.app G)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  have : IsIso
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) hT).counit.app G) :=
    isIso_of_reflects_iso _ (sheafForget X.smallEtaleTopology)
  exact Sheaf.isConstant_of_iso X.smallEtaleTopology
    (asIso ((constantSheafAdj X.smallEtaleTopology
      (ModuleCat.{u + 1} R) hT).counit.app G)).symm

end AlgebraicGeometry.Scheme
