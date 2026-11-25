/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.PushforwardCoherentOnOpen
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.ClosedSupportPushforwardSupport
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Direct image of a formal system with closed ambient support

Source: Stacks Project, Theorem 088E and Lemma 0CYJ.
(blueprint: lem-weil-pbc-formal-system-closed-support-pushforward)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Transport to the open image, apply coherent pushforward there, and transport back. -/
private theorem coherent_pushforward_closed_support {Y X : Scheme.{u}} [IsNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (F : Y.Modules)
    (T : TopologicalSpace.Closeds X) (hT : (T : Set X) ⊆ Set.range j.base)
    (hSupp : {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} ⊆ j.base ⁻¹' (T : Set X))
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace ((Scheme.Modules.pushforward j).obj F) := by
  let U := j.opensRange
  let e := j.isoOpensRange
  let H := (Scheme.Modules.pushforward e.hom).obj F
  let S := T.preimage U.ι.continuous
  have hS : {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} ⊆ e.hom.base ⁻¹' (S : Set _) := by
    intro y hy
    change (e.hom ≫ U.ι) y ∈ (T : Set X)
    rw [show e.hom ≫ U.ι = j from j.isoOpensRange_hom_ι]
    exact hSupp hy
  have hs := Scheme.Modules.pushforward_support_subset_of_closed_support e.hom F S hS
  have hH := (Scheme.Modules.isCoherent_pushforward_of_isFinite e.hom F hF).1
  have hG := (Scheme.Modules.pushforward_coherent_on_open X U T hT H hH hs).1
  let a : (Scheme.Modules.pushforward U.ι).obj H ≅
      (Scheme.Modules.pushforward j).obj F :=
    ((Scheme.Modules.pushforwardComp e.hom U.ι) ≪≫
      Scheme.Modules.pushforwardCongr j.isoOpensRange_hom_ι).app F
  exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2 _ _ a hG

open CategoryTheory.Limits in
/-- Pull back the product inclusion and use the adjunction to detect that it is zero. -/
private theorem powerProduct_pushforward_zero {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData) (F : Y.Modules)
    (hG : ((Scheme.Modules.pushforward j).obj F).IsQuasicoherent) (n : ℕ)
    (hF : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (K.comap j).toModulesι n).2 F)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι n).2
      ((Scheme.Modules.pushforward j).obj F)) := by
  let L := Scheme.Modules.tensorPullback j
  let R := Scheme.Modules.pushforward j
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction j
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have hi : IsIso (adj.counit.app F) := by infer_instance
  have hz : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (K.comap j).toModulesι n).2 (L.obj (R.obj F))) :=
    idealModuleProduct_zero_of_mono _ (adj.counit.app F) hF
  let b := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι n).2 (R.obj F)
  have hb : L.map b = 0 := by
    have h := modulePullbackIdealPowerProductImage j K (R.obj F) hG n
    have hι := hz.eq_zero_of_src
      (Scheme.idealModuleProductι (Scheme.idealSheafPower (K.comap j).toModulesι n).2
        (L.obj (R.obj F)))
    have hbot : imageSubobject (L.map b) = ⊥ := by rw [h, hι, imageSubobject_zero]
    have ha : (imageSubobject (L.map b)).arrow = 0 :=
      Subobject.mk_eq_bot_iff_zero.mp (by simpa using hbot)
    calc
      L.map b = factorThruImageSubobject (L.map b) ≫
          (imageSubobject (L.map b)).arrow := (imageSubobject_arrow_comp _).symm
      _ = 0 := by rw [ha]; simp
  have hb' : b = 0 := by
    apply (adj.homEquiv _ F).symm.injective
    change L.map b ≫ adj.counit.app F = L.map 0 ≫ adj.counit.app F
    rw [hb, Functor.map_zero]
  have : Mono b := idealModuleProduct_mono _ _
  exact IsZero.of_mono_eq_zero b hb'

open CategoryTheory.Limits in
/-- The restriction unit is invertible on the open image and between zero modules
on the complement of the closed support. -/
private theorem supported_restriction_unit_isIso {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (G : X.Modules)
    (T : TopologicalSpace.Closeds X) (hT : (T : Set X) ⊆ Set.range j.base)
    (hSupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X)) :
    IsIso ((Scheme.Modules.restrictAdjunction j).unit.app G) := by
  classical
  let L := Scheme.Modules.restrictFunctor j
  let R := Scheme.Modules.pushforward j
  let η := (Scheme.Modules.restrictAdjunction j).unit.app G
  let U := j.opensRange
  have hU : U ⊔ T.compl = ⊤ := by
    apply le_antisymm le_top
    intro x _
    by_cases hx : x ∈ (T : Set X)
    · exact Or.inl (hT hx)
    · exact Or.inr hx
  have hL : IsIso (L.map η) := by
    have he := (Scheme.Modules.restrictAdjunction j).left_triangle_components G
    have hc : IsIso ((Scheme.Modules.restrictAdjunction j).counit.app (L.obj G)) :=
      inferInstance
    have : IsIso (L.map η ≫ (Scheme.Modules.restrictAdjunction j).counit.app (L.obj G)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictAdjunction j).counit.app (L.obj G))
  have hηU : IsIso ((Scheme.Modules.restrictFunctor U.ι).map η) := by
    let e := j.isoOpensRange
    have hcomp : IsIso ((L ⋙ Scheme.Modules.restrictFunctor e.inv).map η) := by
      change IsIso ((Scheme.Modules.restrictFunctor e.inv).map (L.map η))
      infer_instance
    let a : L ⋙ Scheme.Modules.restrictFunctor e.inv ≅
        Scheme.Modules.restrictFunctor U.ι :=
      (Scheme.Modules.restrictFunctorComp e.inv j).symm ≪≫
        Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp
    exact (NatIso.isIso_map_iff a η).mp hcomp
  have hs : IsZero ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι T.compl)).obj G) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    ext V s
    change s = 0
    apply TopCat.Presheaf.section_ext ⟨G.presheaf, G.isSheaf⟩
    intro x hx
    have hxT : x ∉ (T : Set X) := Scheme.Opens.ι_image_le T.compl V hx
    have : Subsingleton (G.presheaf.stalk x) := by
      by_contra hn
      exact hxT (hSupp hn)
    exact this.elim _ _
  have ht : IsZero
      ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι T.compl)).obj (R.obj (L.obj G))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    ext V s
    change s = 0
    refine TopCat.Presheaf.section_ext ⟨G.presheaf, G.isSheaf⟩
      (j ''ᵁ (j ⁻¹ᵁ ((Scheme.Opens.ι T.compl) ''ᵁ V))) s 0 ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hxT : j y ∉ (T : Set X) := Scheme.Opens.ι_image_le T.compl V hy
    have : Subsingleton (G.presheaf.stalk (j y)) := by
      by_contra hn
      exact hxT (hSupp hn)
    exact this.elim _ _
  have hηT : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι T.compl)).map η) :=
    isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
  let W : ULift.{u} Bool → X.Opens := fun i ↦ if i.down then U else T.compl
  have hW : ⨆ i, W i = ⊤ := by
    apply le_antisymm le_top
    rw [← hU]
    apply sup_le
    · exact le_iSup_of_le (ULift.up true) (by simp [W])
    · exact le_iSup_of_le (ULift.up false) (by simp [W])
  apply (sheaf_module_isIso_iff_isIso_over_open_cover X.toRingedSpace
    (ULift.{u} Bool) W hW _ _ η).mpr
  intro i
  have hr : IsIso ((Scheme.Modules.restrictFunctor (W i).ι).map η) := by
    cases i with
    | up b =>
      cases b
      · exact hηT
      · exact hηU
  let a := Scheme.Modules.overFunctorEquiv (W i)
  have ho : IsIso (((SheafOfModules.overFunctor X.ringCatSheaf (W i)) ⋙
      (Scheme.Modules.overEquiv (W i)).functor).map η) := by
    exact (NatIso.isIso_map_iff a η).mpr hr
  have ho' : IsIso ((Scheme.Modules.overEquiv (W i)).functor.map
      (η.over (W i))) := ho
  exact isIso_of_reflects_iso _ (Scheme.Modules.overEquiv (W i)).functor

open CategoryTheory.Limits in
/-- The quotient has the same closed ambient support. Its invertible adjunction unit,
the pullback quotient comparison, and the counit construct the direct-image comparison. -/
private theorem powerQuotient_pushforward_iso {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData) (F : Y.Modules)
    (hG : ((Scheme.Modules.pushforward j).obj F).IsQuasicoherent)
    (T : TopologicalSpace.Closeds X) (hT : (T : Set X) ⊆ Set.range j.base)
    (hSupp : {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} ⊆ j.base ⁻¹' (T : Set X))
    (n : ℕ) :
    ∃ e : formalModuleQuotient K n ((Scheme.Modules.pushforward j).obj F) ≅
        (Scheme.Modules.pushforward j).obj (formalModuleQuotient (K.comap j) n F),
      formalModuleQuotientπ K n ((Scheme.Modules.pushforward j).obj F) ≫ e.hom =
        (Scheme.Modules.pushforward j).map (formalModuleQuotientπ (K.comap j) n F) := by
  let L := Scheme.Modules.tensorPullback j
  let R := Scheme.Modules.pushforward j
  let G := R.obj F
  let Q := formalModuleQuotient K n G
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction j
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : IsIso (adj.counit.app F) := inferInstance
  have hQ : {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ (T : Set X) := by
    intro x hx
    apply Scheme.Modules.pushforward_support_subset_of_closed_support j F T hSupp
    intro hzero
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let i := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι n).2 G
    have : Epi (S.map (cokernel.π i)) :=
      ((RingedSpace.module_stalk_exact X.toRingedSpace i).2.2.1 x).1
    have : Subsingleton (S.obj G) := hzero
    have hquot : Subsingleton (S.obj (cokernel i)) :=
      Function.Surjective.subsingleton
        ((ModuleCat.epi_iff_surjective (S.map (cokernel.π i))).mp inferInstance)
    exact hx hquot
  have hu : IsIso (adj.unit.app Q) := by
    have : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app Q) :=
      supported_restriction_unit_isIso j Q T hT hQ
    rw [← Adjunction.unit_leftAdjointUniq_hom_app
      (Scheme.Modules.restrictAdjunction j) adj Q]
    infer_instance
  let B : Y.Modules ⥤ Y.Modules :=
    { obj := formalModuleQuotient (K.comap j) n
      map := fun f ↦ formalModuleQuotientMap (K.comap j) f (Nat.le_refl n)
      map_id := fun A ↦ formalModuleQuotientMap_id (K.comap j) A n
      map_comp := fun f g ↦ formalModuleQuotientMap_comp (K.comap j) f g
        (Nat.le_refl n) (Nat.le_refl n) }
  let p := powerQuotientIso j K G hG n
  let a : L.obj Q ≅ formalModuleQuotient (K.comap j) n F :=
    p.symm ≪≫ B.mapIso (asIso (adj.counit.app F))
  refine ⟨asIso (adj.unit.app Q) ≪≫ R.mapIso a, ?_⟩
  change formalModuleQuotientπ K n G ≫ adj.unit.app Q ≫ R.map a.hom =
    R.map (formalModuleQuotientπ (K.comap j) n F)
  have hn : formalModuleQuotientπ K n G ≫ adj.unit.app Q =
      adj.unit.app G ≫ R.map (L.map (formalModuleQuotientπ K n G)) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (adj.unit.naturality (formalModuleQuotientπ K n G))
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← R.map_comp]
  have ha : L.map (formalModuleQuotientπ K n G) ≫ a.hom =
      adj.counit.app F ≫ formalModuleQuotientπ (K.comap j) n F := by
    dsimp only [a, p, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
    rw [← powerQuotientIso_π j K G hG n]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact quotientMap_π (K.comap j) (adj.counit.app F) (Nat.le_refl n)
  rw [ha, R.map_comp, ← Category.assoc, adj.right_triangle_components F]
  exact Category.id_comp _

/-- Direct image along an open immersion preserves the coherent adic conditions when
all levels have support in a fixed closed subset of the ambient scheme contained in
that open immersion's image.

Source: Stacks Project, coherent.tex, Theorem 088E (theorem-grothendieck-existence),
the extension paragraph, and Lemma 0CYJ (lemma-pushforward-coherent-on-open).
(blueprint: lem-weil-pbc-formal-system-closed-support-pushforward)

Proof: Identify Y with the open image U of j. Lemma 0CYJ makes every j_*F_n coherent
and zero on X minus T. On U the restriction/direct-image counit identifies the entire
system, including its transitions, with F. Restriction of K identifies its products
and positive powers with those of K.comap j; restriction preserves cokernels.
Thus on U the power-product annihilation and quotient-transition conditions are those
of F. On X minus T all modules and their products and quotients are zero. These two
opens cover X since T lies in U. Vanishing of the power products is local. Each
transition therefore kills its indicated ideal-power product globally and factors
through its cokernel. This factor restricts to an isomorphism on each of the two
opens, so it is globally an isomorphism. These factors have the required equations
with quotient projections by construction. -/
theorem coherentFormal_pushforward_of_closed_support
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData)
    (F : ℕᵒᵖ ⥤ Y.Modules) (T : TopologicalSpace.Closeds X)
    (hT : (T : Set X) ⊆ Set.range j.base)
    (hSupp : ∀ n : ℕ,
      {y : Y | ¬ Subsingleton ((F.obj (op n)).presheaf.stalk y)} ⊆
        j.base ⁻¹' (T : Set X))
    (hF : IsCoherentFormalModule (K.comap j) F) :
    IsCoherentFormalModule K (F ⋙ Scheme.Modules.pushforward j) := by
  have hcoh (n : ℕ) := coherent_pushforward_closed_support j (F.obj (op n)) T hT
    (hSupp n) (hF.1 n)
  have hq (n : ℕ) : ((Scheme.Modules.pushforward j).obj (F.obj (op n))).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp (hcoh n)).1
  refine ⟨hcoh, ?_, ?_⟩
  · intro n
    exact powerProduct_pushforward_zero j K (F.obj (op n)) (hq n) (n + 1) (hF.2.1 n)
  · intro n
    obtain ⟨a, ha⟩ := powerQuotient_pushforward_iso j K (F.obj (op (n + 1)))
      (hq (n + 1)) T hT (hSupp (n + 1)) (n + 1)
    obtain ⟨b, hb⟩ := hF.2.2 n
    refine ⟨a ≪≫ (Scheme.Modules.pushforward j).mapIso b, ?_⟩
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map]
    rw [← Category.assoc, ha, ← Functor.map_comp, hb]

end AlgebraicGeometry
