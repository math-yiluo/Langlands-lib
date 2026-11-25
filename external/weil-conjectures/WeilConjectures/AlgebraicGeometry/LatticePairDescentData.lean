/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
public import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
/-!
# Compatible tuples for integral lattice descent

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60.
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective
universe u c v s
open CategoryTheory Opposite
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
private noncomputable def flattenOverModuleIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{s}) (W : C) (Z : Over W) (M : SheafOfModules.{s} R) :
    (SheafOfModules.pushforward (F := Z.iteratedSliceBackward) (𝟙 _)).obj
      ((M.over W).over Z) ≅ M.over Z.left :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun T ↦ Iso.refl _) (by
      intro T T' f
      ext m
      rfl))

private theorem finiteLocallyFree_of_cover
    {C : Type (max c v)} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{s}}
    [∀ W, HasSheafify (J.over W) AddCommGrpCat.{s}]
    [∀ W, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{s}]
    [∀ W (Z : Over W), HasSheafify ((J.over W).over Z) AddCommGrpCat.{s}]
    [∀ W (Z : Over W), ((J.over W).over Z).WEqualsLocallyBijective AddCommGrpCat.{s}]
    (M : SheafOfModules.{s} R) {I : Type (max c v)} (W : I → C) (hW : J.CoversTop W)
    (hm : ∀ i, (M.over (W i)).IsFiniteLocallyFree) : M.IsFiniteLocallyFree := by
  classical
  choose q hq hf using fun i : I ↦ (hm i).exists_localGeneratorsData
  let := hq
  let := hf
  let I' := Σ i : I, (q i).I
  let Y : I' → C := fun j ↦ ((q j.1).X j.2).left
  have hY : J.CoversTop Y := hW.over (fun i ↦ (q i).coversTop)
  let κ (j : I') := ((q j.1).generators j.2).I
  have (j : I') : Finite (κ j) :=
    let := (hf j.1).isFiniteType j.2
    inferInstance
  refine isFiniteLocallyFree_of_exists_over_iso_free (M := M) Y hY κ ?_
  intro j
  let Z := (q j.1).X j.2
  let H := Z.iteratedSliceBackward
  have : H.IsEquivalence := inferInstanceAs Z.iteratedSliceEquiv.inverse.IsEquivalence
  let T : SheafOfModules.{s} ((R.over (W j.1)).over Z) ⥤
      SheafOfModules.{s} (R.over (Y j)) :=
    SheafOfModules.pushforward (F := H) (𝟙 _)
  have he : T.obj ((M.over (W j.1)).over Z) ≅ M.over (Y j) :=
    flattenOverModuleIso R (W j.1) Z M
  exact ⟨he.symm ≪≫ T.mapIso (asIso ((q j.1).generators j.2).π).symm ≪≫
    (mapFreeIso T (κ j) (Iso.refl _)).symm⟩
end SheafOfModules

namespace AlgebraicGeometry.ProEtale

attribute [local instance] restrictionStrongSheafifyOver restrictionWeakSheafifyOverOver
  restrictionWEqualsOverOver restrictionStrongSheafifyOverOver

set_option backward.isDefEq.respectTransparency false

section
variable {A M N P : Type*} [Ring A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]
noncomputable def commonImageEquiv (f : M →ₗ[A] P) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : LinearMap.range f = LinearMap.range g) : M ≃ₗ[A] N :=
  (LinearEquiv.ofInjective f hf).trans
    ((LinearEquiv.ofEq _ _ h).trans (LinearEquiv.ofInjective g hg).symm)
theorem commonImageEquiv_spec (f : M →ₗ[A] P) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : LinearMap.range f = LinearMap.range g) (m : M) :
    g (commonImageEquiv f g hf hg h m) = f m := by
  change g ((LinearEquiv.ofInjective g hg).symm _) = f m
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl
end

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  (ha : ∀ (U : X.ProEt) T,
    Function.Injective (((latticeScalarMap a U).hom.app T).hom))
  (U : X.ProEt) (r : Sieve U)
  (x : Presieve.FamilyOfElements (latticeClassPresheaf a L) r.arrows)
  (hx : x.Compatible)

abbrev latticeCoverIndex := Σ V : X.ProEt, {f : V ⟶ U // r f}
abbrev latticeCoverObject (i : latticeCoverIndex U r) : Over U := Over.mk i.2.val
noncomputable def latticeCoverPair (i : latticeCoverIndex U r) :
    IntegralLatticePair a L i.1 := (x i.2.val i.2.property).down.property.choose

theorem latticeCoverPair_image (i : latticeCoverIndex U r) (T : Over i.1) :
    (latticeCoverPair a L U r x i).image (op T) =
      (x i.2.val i.2.property).down.val T :=
  (x i.2.val i.2.property).down.property.choose_spec T

noncomputable def latticeCoverModule (i : latticeCoverIndex U r) :
    SheafOfModules.{u + 1}
      ((((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U).over
        (latticeCoverObject U r i)) := by
  letI : (latticeCoverObject U r i).iteratedSliceForward.IsContinuous
      (((Scheme.ProEt.topology X).over U).over (latticeCoverObject U r i))
      ((Scheme.ProEt.topology X).over i.1) :=
    inferInstanceAs ((latticeCoverObject U r i).iteratedSliceForward.IsContinuous
      _ ((Scheme.ProEt.topology X).over (latticeCoverObject U r i).left))
  exact (SheafOfModules.pushforward (F := (latticeCoverObject U r i).iteratedSliceForward)
    (𝟙 _)).obj (latticeCoverPair a L U r x i).module

set_option hygiene false in
local notation "𝓡" => (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
set_option hygiene false in
local notation "N" => (SheafOfModules.restrictScalars.{u + 1}
  ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (latticeScalarMap a U))).obj (L.over U)

noncomputable def latticeCoverEmbedding (i : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i) :
    (latticeCoverModule a L U r x i).val.obj (op (Over.mk b)) ⟶ (N).val.obj (op W) :=
  (pairEmbedding a L i.1 (latticeCoverPair a L U r x i)).val.app (op (Over.mk b.left))

include ha in
theorem latticeCoverEmbedding_injective (i : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i) :
    Function.Injective (latticeCoverEmbedding a L U r x i W b) :=
  IntegralLatticePair.embedding_injective a L i.1 (ha i.1)
    (latticeCoverPair a L U r x i) (op (Over.mk b.left))

include hx in
theorem latticeCoverEmbedding_range (i j : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i)
    (c : W ⟶ latticeCoverObject U r j) :
    LinearMap.range (latticeCoverEmbedding a L U r x i W b).hom =
      LinearMap.range (latticeCoverEmbedding a L U r x j W c).hom := by
  apply Submodule.ext
  intro z
  change z ∈ (latticeCoverPair a L U r x i).image (op (Over.mk b.left)) ↔
    z ∈ (latticeCoverPair a L U r x j).image (op (Over.mk c.left))
  rw [latticeCoverPair_image, latticeCoverPair_image]
  have h := hx b.left c.left i.2.property j.2.property
    ((Over.w b).trans (Over.w c).symm)
  have h' := congrArg (fun s ↦ s.down.val (Over.mk (𝟙 W.left))) h
  change (x i.2.val i.2.property).down.val (Over.mk (𝟙 W.left ≫ b.left)) =
    (x j.2.val j.2.property).down.val (Over.mk (𝟙 W.left ≫ c.left)) at h'
  rw [Category.id_comp, Category.id_comp] at h'
  rw [h']

noncomputable def latticeCoverTransition (i j : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i)
    (c : W ⟶ latticeCoverObject U r j) :
    (latticeCoverModule a L U r x i).val.obj (op (Over.mk b)) ≃ₗ[
      ((𝓡).over U).obj.obj (op W)]
        (latticeCoverModule a L U r x j).val.obj (op (Over.mk c)) :=
  commonImageEquiv (latticeCoverEmbedding a L U r x i W b).hom
    (latticeCoverEmbedding a L U r x j W c).hom
    (latticeCoverEmbedding_injective a L ha U r x i W b)
    (latticeCoverEmbedding_injective a L ha U r x j W c)
    (latticeCoverEmbedding_range a L U r x hx i j W b c)

theorem latticeCoverTransition_spec (i j : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i)
    (c : W ⟶ latticeCoverObject U r j)
    (m : (latticeCoverModule a L U r x i).val.obj (op (Over.mk b))) :
    latticeCoverEmbedding a L U r x j W c
      (latticeCoverTransition a L ha U r x hx i j W b c m) =
        latticeCoverEmbedding a L U r x i W b m :=
  commonImageEquiv_spec _ _ _ _ _ m

theorem latticeCoverEmbedding_naturality (i : latticeCoverIndex U r)
    (W V : Over U) (k : V ⟶ W) (b : W ⟶ latticeCoverObject U r i)
    (m : (latticeCoverModule a L U r x i).val.obj (op (Over.mk b))) :
    latticeCoverEmbedding a L U r x i V (k ≫ b)
      ((latticeCoverModule a L U r x i).val.map
        (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op m) =
      (N).val.map k.op (latticeCoverEmbedding a L U r x i W b m) := by
  exact PresheafOfModules.naturality_apply
    (pairEmbedding a L i.1 (latticeCoverPair a L U r x i)).val
    (Over.homMk (U := Over.mk (k.left ≫ b.left)) (V := Over.mk b.left) k.left rfl).op m

noncomputable def latticeModuleGlueData :
    SheafOfModules.ModuleGlueData.{u + 1, u, u + 1, u + 1, u + 1}
      ((𝓡).over U) (latticeCoverObject U r) where
  localSheaf := latticeCoverModule a L U r x
  transition := fun i j W b c ↦
    (latticeCoverTransition a L ha U r x hx i j W b c).toAddEquiv
  transition_smul := fun i j W b c s m ↦
    (latticeCoverTransition a L ha U r x hx i j W b c).map_smul s m
  naturality := by
    intro i j W V k b c m
    apply latticeCoverEmbedding_injective a L ha U r x j V (k ≫ c)
    change latticeCoverEmbedding a L U r x j V (k ≫ c)
      (latticeCoverTransition a L ha U r x hx i j V (k ≫ b) (k ≫ c) _) = _
    rw [latticeCoverTransition_spec, latticeCoverEmbedding_naturality,
      latticeCoverEmbedding_naturality]
    exact congrArg ((N).val.map k.op)
      (latticeCoverTransition_spec a L ha U r x hx i j W b c m).symm
  cocycle := by
    intro i j k W b c d m
    apply latticeCoverEmbedding_injective a L ha U r x k W d
    change latticeCoverEmbedding a L U r x k W d
      (latticeCoverTransition a L ha U r x hx i k W b d m) = _
    rw [latticeCoverTransition_spec]
    exact ((latticeCoverTransition_spec a L ha U r x hx j k W c d
      (latticeCoverTransition a L ha U r x hx i j W b c m)).trans
        (latticeCoverTransition_spec a L ha U r x hx i j W b c m)).symm

noncomputable def gluedLatticeModule : SheafOfModules.{u + 1} ((𝓡).over U) :=
  (latticeModuleGlueData a L ha U r x hx).sheaf
    (latticeModuleGlueData a L ha U r x hx).presheaf_isSheaf

noncomputable def gluedLatticeModuleLocalIso (i : latticeCoverIndex U r) :
    (gluedLatticeModule a L ha U r x hx).over (latticeCoverObject U r i) ≅
      latticeCoverModule a L U r x i :=
  (latticeModuleGlueData a L ha U r x hx).overIso
    (latticeModuleGlueData a L ha U r x hx).presheaf_isSheaf i

theorem gluedLatticeModule_overlap (i j : latticeCoverIndex U r)
    (W : Over U) (b : W ⟶ latticeCoverObject U r i)
    (c : W ⟶ latticeCoverObject U r j)
    (m : (gluedLatticeModule a L ha U r x hx).val.obj (op W)) :
    latticeCoverTransition a L ha U r x hx i j W b c
      ((gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app (op (Over.mk b)) m) =
      (gluedLatticeModuleLocalIso a L ha U r x hx j).hom.val.app (op (Over.mk c)) m := by
  exact m.2.2 i j W (𝟙 W) b c

theorem latticeCoverModule_finiteLocallyFree (i : latticeCoverIndex U r) :
    (latticeCoverModule a L U r x i).IsFiniteLocallyFree := by
  classical
  let Z := latticeCoverObject U r i
  let J := ((Scheme.ProEt.topology X).over U).over Z
  let K := (Scheme.ProEt.topology X).over i.1
  let F := Z.iteratedSliceForward
  have : F.IsEquivalence := inferInstanceAs Z.iteratedSliceEquiv.functor.IsEquivalence
  have : F.IsContinuous J K := inferInstanceAs (F.IsContinuous J
    ((Scheme.ProEt.topology X).over Z.left))
  have : F.IsCocontinuous J K := inferInstanceAs (F.IsCocontinuous J
    ((Scheme.ProEt.topology X).over Z.left))
  have hp := (latticeCoverPair a L U r x i).locallyFree
  obtain ⟨q, hq, hf⟩ := hp.exists_localGeneratorsData
  let := hq
  let := hf
  let I := Σ j : q.I, Σ W : Over Z, (F.obj W ⟶ q.X j)
  let W : I → Over Z := fun j ↦ j.2.1
  have hW : J.CoversTop W := by
    intro T
    apply J.superset_covering _ (F.cover_lift J K (q.coversTop (F.obj T)))
    intro T' g hg
    obtain ⟨j, ⟨t⟩⟩ := hg
    exact ⟨⟨j, T', t⟩, ⟨𝟙 T'⟩⟩
  let κ (j : I) := (q.generators j.1).I
  have (j : I) : Finite (κ j) :=
    let := hf.isFiniteType j.1
    inferInstance
  apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free W hW κ
  intro j
  let H := Over.post (X := W j) F ⋙ Over.map j.2.2
  have : (Over.post (X := W j) F).IsEquivalence := inferInstance
  have : (Over.post (X := W j) F).IsContinuous (J.over (W j))
      (K.over (F.obj (W j))) :=
    (Functor.isContinuous_iff_coverPreserving
      (J := J.over (W j)) (K := K.over (F.obj (W j)))
      (F := Over.post (X := W j) F)).mpr
        ((CoverPreserving.of_isContinuous F J K).overPost (W j))
  have : H.IsContinuous (J.over (W j)) (K.over (q.X j.1)) :=
    Functor.isContinuous_comp _ _ _ (K.over (F.obj (W j))) _
  have : H.IsCocontinuous (J.over (W j)) (K.over (q.X j.1)) :=
    isCocontinuous_comp _ _ (J.over (W j)) (K.over (F.obj (W j)))
  have : H.IsLeftAdjoint := by
    dsimp [H, F]
    infer_instance
  let T : SheafOfModules.{u + 1} (((𝓡).over i.1).over (q.X j.1)) ⥤
      SheafOfModules.{u + 1} ((((𝓡).over U).over Z).over (W j)) :=
    SheafOfModules.pushforward (F := H) (𝟙 _)
  have he : T.obj ((latticeCoverPair a L U r x i).module.over (q.X j.1)) ≅
      (latticeCoverModule a L U r x i).over (W j) := Iso.refl _
  exact ⟨he.symm ≪≫ T.mapIso (asIso (q.generators j.1).π).symm ≪≫
    (SheafOfModules.mapFreeIso T (κ j) (Iso.refl _)).symm⟩

theorem latticeCover_coversTop (hr : r ∈ (Scheme.ProEt.topology X) U) :
    ((Scheme.ProEt.topology X).over U).CoversTop (latticeCoverObject U r) := by
  intro W
  apply ((Scheme.ProEt.topology X).over U).superset_covering _
    ((Scheme.ProEt.topology X).overEquiv_symm_mem_over W _
      ((Scheme.ProEt.topology X).pullback_stable W.hom hr))
  intro T g hg
  have ht : r T.hom := by
    change r (g.left ≫ W.hom) at hg
    rwa [Over.w g] at hg
  exact ⟨⟨T.left, T.hom, ht⟩, ⟨Over.homMk (𝟙 T.left) (by simp)⟩⟩

theorem finiteLocallyFree_of_latticeCover
    (M : SheafOfModules.{u + 1} ((𝓡).over U))
    (hr : r ∈ (Scheme.ProEt.topology X) U)
    (hm : ∀ i : latticeCoverIndex U r,
      (M.over (latticeCoverObject U r i)).IsFiniteLocallyFree) :
    M.IsFiniteLocallyFree := by
  exact SheafOfModules.finiteLocallyFree_of_cover.{u + 1, u, u + 1} M (latticeCoverObject U r)
    (latticeCover_coversTop U r hr) hm

include hx in
/-- The compatible-tuple integral module is finite locally free.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices.
(auxiliary; not a blueprint node).
Proof: each tuple projection identifies the restricted module with the chosen
local lattice. Transport its finite free basis covers along the iterated-slice
equivalence. Compose those basis covers with the original covering sieve to
obtain a finite free basis cover of the glued module; ranks may vary. -/
theorem gluedLatticeModule_finiteLocallyFree
    (hr : r ∈ (Scheme.ProEt.topology X) U) :
    (gluedLatticeModule a L ha U r x hx).IsFiniteLocallyFree := by
  apply finiteLocallyFree_of_latticeCover (R := R) U r _ hr
  intro i
  let G := latticeModuleGlueData a L ha U r x hx
  let : (G.localSheaf i).IsFiniteLocallyFree :=
    latticeCoverModule_finiteLocallyFree a L U r x i
  exact SheafOfModules.IsFiniteLocallyFree.of_iso
    (R := ((𝓡).over U).over (latticeCoverObject U r i))
    (G.overIso G.presheaf_isSheaf i).symm

end AlgebraicGeometry.ProEtale
