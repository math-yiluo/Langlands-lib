/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.RingTheory.Spectrum.Prime.Colimit
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The actual inverse limit of a finite étale surjective tower is a cover

Source: blueprint, smooth purity, proof of `definition-tate-twists`, (1);
Stacks Project, Tags 01YX, 01YW, 097N, 090N, 00HP, 00HQ and 094S
(blueprint: lem-pur-finite-etale-surjective-limit-cover).

## Main definitions

* `FiniteEtaleTower.affineDiagram`: the tower restricted to an open of the base.
* `FiniteEtaleTower.ringDiagram`: its contravariant diagram of global sections.
* `FiniteEtaleTower.baseMap`: the canonical map from the base chart to the ring colimit.

## Main statements

* `exists_finiteEtale_surjective_limit_cover`: existence of the actual scheme limit,
  its covering property, and the compatible affine-chart description.

Index `n : ℕ` denotes the paper's positive index `n + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace FiniteEtaleTower

/-- Restriction of a tower over `X` to the open subscheme `U`, by actual fibre products.
Source: Stacks Project, Tags 01YX and 01YW, applied to the tower in blueprint proof (1)
of `definition-tate-twists`
(blueprint: lem-pur-finite-etale-surjective-limit-cover). -/
noncomputable def affineDiagram {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X) (U : X.Opens) :
    ℕᵒᵖ ⥤ Scheme.{u} :=
  D ⋙ Over.pullback U.ι ⋙ Over.forget U.toScheme

/-- The coordinate rings of the base-changed tower, with their actual transition maps.
Source: Stacks Project, Tag 01YW, and blueprint proof (1) of
`definition-tate-twists`
(blueprint: lem-pur-finite-etale-surjective-limit-cover). -/
noncomputable def ringDiagram {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X) (U : X.Opens) :
    ℕᵒᵖᵒᵖ ⥤ CommRingCat.{u} :=
  (affineDiagram D U).op ⋙ Scheme.Γ

/-- The canonical map `A → colim Bₙ`, computed using the first stage. All stages give
this same map because all transitions are over the base chart.
Source: Stacks Project, Tag 01YW, and blueprint proof (1) of
`definition-tate-twists`
(blueprint: lem-pur-finite-etale-surjective-limit-cover). -/
noncomputable def baseMap {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X) (U : X.Opens) :
    Γ(U.toScheme, ⊤) ⟶ colimit (ringDiagram D U) :=
  (pullback.snd (D.obj (op 0)).hom U.ι).appTop ≫
    colimit.ι (ringDiagram D U) (op (op 0))

end FiniteEtaleTower

private theorem finite_map {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (hfinite : ∀ n : ℕ, IsFinite (D.obj (op n)).hom)
    {i j : ℕᵒᵖ} (f : i ⟶ j) : IsFinite (D.map f).left := by
  have : IsFinite (D.obj j).hom := hfinite j.unop
  have : IsFinite ((D.map f).left ≫ (D.obj j).hom) := by
    rw [Over.w]
    exact hfinite i.unop
  exact IsFinite.of_comp _ (D.obj j).hom

private theorem exists_affine_cone {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (hfinite : ∀ n : ℕ, IsFinite (D.obj (op n)).hom) :
    ∃ c : Cone D, Nonempty (IsLimit ((Over.forget X).mapCone c)) ∧
      IsAffineHom c.pt.hom := by
  classical
  let e : ULift.{u} ℕ ≌ ℕ := ULift.orderIso.equivalence
  let F := D ⋙ Over.forget X
  have (i j : ℕᵒᵖ) (f : i ⟶ j) : IsAffineHom (F.map f) := by
    have : IsFinite (D.map f).left := finite_map D hfinite f
    change IsAffineHom (D.map f).left
    infer_instance
  let G := e.functor.op ⋙ F
  have {i j : (ULift.{u} ℕ)ᵒᵖ} (f : i ⟶ j) : IsAffineHom (G.map f) := by
    dsimp [G]
    infer_instance
  obtain ⟨a, ⟨ha⟩⟩ := exists_limit_affine_transition_core G
  let : HasLimit G := ⟨⟨a, ha⟩⟩
  let : HasLimit F := Functor.Initial.hasLimit_of_comp e.functor.op
  let : IsConnected ℕᵒᵖ := IsCofiltered.isConnected _
  let : HasLimit D := hasLimit_of_created D (Over.forget X)
  let c := limit.cone D
  have hc : IsLimit ((Over.forget X).mapCone c) :=
    isLimitOfPreserves (Over.forget X) (limit.isLimit D)
  have hπ : IsAffineHom (c.π.app (op 0)).left :=
    isAffineHom_π_app G _ (hc.whiskerEquivalence e.op)
      (op (ULift.up 0))
  have : IsFinite (D.obj (op 0)).hom := hfinite 0
  have heq : c.pt.hom = (c.π.app (op 0)).left ≫ (D.obj (op 0)).hom :=
    (c.π.app (op 0)).w.symm
  exact ⟨c, ⟨hc⟩, heq ▸ inferInstance⟩

private theorem chart_comparison {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (U : X.Opens) (ha : ∀ n : ℕ,
      IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n))) :
    ∃ e : pullback c.pt.hom U.ι ≅ Spec (colimit (FiniteEtaleTower.ringDiagram D U)),
      ∀ n : ℕ,
        e.hom ≫ Spec.map (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op n))) =
          ((Over.pullback U.ι).map (c.π.app (op n))).left ≫
            ΓSpec.adjunction.unit.app ((FiniteEtaleTower.affineDiagram D U).obj (op n)) := by
  have (n : ℕᵒᵖ) :
      IsAffine (((D ⋙ Over.pullback U.ι) ⋙ Over.forget U.toScheme).obj n) := ha n.unop
  have (n : ℕᵒᵖᵒᵖ) :
      IsAffine ((((D ⋙ Over.pullback U.ι) ⋙ Over.forget U.toScheme).op.obj n).unop) :=
    ha n.unop.unop
  let : IsConnected ℕᵒᵖ := IsCofiltered.isConnected _
  have hc' : IsLimit c := isLimitOfReflects (Over.forget X) hc
  let a := (Over.forget U.toScheme).mapCone ((Over.pullback U.ι).mapCone c)
  have ha' : IsLimit a := isLimitOfPreserves (Over.pullback U.ι ⋙ Over.forget _) hc'
  have : IsAffine a.pt := Scheme.isAffine_of_isLimit a ha'
  let hΓ := isColimitOfPreserves Scheme.Γ ha'.op
  let eΓ := hΓ.coconePointUniqueUpToIso
    (colimit.isColimit (FiniteEtaleTower.ringDiagram D U))
  refine ⟨a.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op, ?_⟩
  intro n
  change a.pt.isoSpec.hom ≫ Spec.map eΓ.inv ≫ Spec.map
    (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op n))) = _
  rw [← Spec.map_comp]
  have hι := hΓ.comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit (FiniteEtaleTower.ringDiagram D U)) (op (op n))
  change colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op n)) ≫ eΓ.inv =
    (a.π.app (op n)).appTop at hι
  rw [hι]
  exact Scheme.isoSpec_hom_naturality (X := a.pt)
    (Y := (FiniteEtaleTower.affineDiagram D U).obj (op n)) (a.π.app (op n))

private theorem chart_proEtale {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (hetale : ∀ n : ℕ, Etale (D.obj (op n)).hom)
    (U : X.Opens) (ha : ∀ n : ℕ,
      IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n))) :
    WeaklyEtale (pullback.snd c.pt.hom U.ι) := by
  let e : ULift.{u} ℕ ≌ ℕ := ULift.orderIso.equivalence
  let : IsCofiltered (ULift.{u} ℕ)ᵒᵖ := IsCofiltered.of_equivalence e.op.symm
  let : IsConnected ℕᵒᵖ := IsCofiltered.isConnected _
  let a := (Over.pullback U.ι).mapCone c
  have ha' : IsLimit ((Over.forget _).mapCone a) :=
    isLimitOfPreserves (Over.pullback U.ι ⋙ Over.forget _)
      (isLimitOfReflects (Over.forget X) hc)
  apply proAffineEtale_le_weaklyEtale
  refine ⟨(ULift.{u} ℕ)ᵒᵖ, inferInstance, inferInstance,
    e.functor.op ⋙ FiniteEtaleTower.affineDiagram D U,
    (Functor.whiskerLeft (e.functor.op ⋙ D ⋙ Over.pullback U.ι)
      (Over.forgetCocone U.toScheme).ι),
    (Functor.whiskerLeft e.functor.op ((Over.forget _).mapCone a).π),
    ha'.whiskerEquivalence e.op, ?_⟩
  intro i
  have : Etale (D.obj (op i.unop.down)).hom := hetale i.unop.down
  refine ⟨⟨?_, ha i.unop.down, trivial⟩, (a.π.app (op i.unop.down)).w⟩
  change Etale (pullback.snd (D.obj (op i.unop.down)).hom U.ι)
  infer_instance

private theorem chart_iota_surjective {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (htransitionSurjective : ∀ n : ℕ,
      Surjective (D.map (homOfLE (Nat.le_succ n)).op).left)
    (U : X.Opens) (ha : ∀ n : ℕ,
      IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n))) :
    Surjective (Spec.map
      (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op 0)))) := by
  let F := FiniteEtaleTower.affineDiagram D U
  let (n : ℕᵒᵖ) : IsAffine (F.obj n) := ha n.unop
  let G := (opOp ℕ) ⋙ FiniteEtaleTower.ringDiagram D U
  have hG (n : ℕ) : Function.Surjective
      (PrimeSpectrum.comap (G.map (homOfLE (Nat.le_succ n))).hom) := by
    let f := F.map (homOfLE (Nat.le_succ n)).op
    have hf : Surjective f := MorphismProperty.overPullbackMap
      (P := @Surjective) U.ι _ (htransitionSurjective n)
    have heq : Spec.map f.appTop = (F.obj (op (n + 1))).isoSpec.inv ≫
        f ≫ (F.obj (op n)).isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have : Surjective (Spec.map f.appTop) := by
      rw [heq]
      infer_instance
    exact this.surj
  have : Surjective (Spec.map (colimit.ι G 0)) :=
    ⟨PrimeSpectrum.comap_colimit_ι_zero_surjective G hG⟩
  have heq := colimit.ι_pre (FiniteEtaleTower.ringDiagram D U) (opOp ℕ) 0
  change Surjective (Spec.map
    (colimit.ι (FiniteEtaleTower.ringDiagram D U) ((opOp ℕ).obj 0)))
  rw [← heq, Spec.map_comp]
  infer_instance

private theorem chart_base_equation {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ Over X)
    (c : Cone D) (U : X.Opens)
    (e : pullback c.pt.hom U.ι ≅ Spec (colimit (FiniteEtaleTower.ringDiagram D U)))
    (h : e.hom ≫ Spec.map
      (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op 0))) =
      ((Over.pullback U.ι).map (c.π.app (op 0))).left ≫
        ΓSpec.adjunction.unit.app ((FiniteEtaleTower.affineDiagram D U).obj (op 0))) :
    e.hom ≫ Spec.map (FiniteEtaleTower.baseMap D U) =
      pullback.snd c.pt.hom U.ι ≫ ΓSpec.adjunction.unit.app U.toScheme := by
  rw [FiniteEtaleTower.baseMap, Spec.map_comp, ← Category.assoc, h, Category.assoc]
  have hn :
      ΓSpec.adjunction.unit.app ((FiniteEtaleTower.affineDiagram D U).obj (op 0)) ≫
        Spec.map (pullback.snd (D.obj (op 0)).hom U.ι).appTop =
      pullback.snd (D.obj (op 0)).hom U.ι ≫ ΓSpec.adjunction.unit.app U.toScheme :=
    ΓSpec.adjunction.unit_naturality (pullback.snd (D.obj (op 0)).hom U.ι)
  rw [hn, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ ΓSpec.adjunction.unit.app U.toScheme)
    ((Over.pullback U.ι).map (c.π.app (op 0))).w

/-- The inverse limit of a tower of finite étale surjections over an arbitrary scheme
is an affine surjective weakly étale cover, with its actual affine coordinate colimits.
The cone is limiting after forgetting to schemes; its legs are the specified projections.
The singleton belongs to the precoverage of the small pro-étale site. The chart
isomorphism respects every projection and the structure morphism to the base chart.

Source: blueprint proof (1) of `definition-tate-twists`;
Stacks Project, Tags 01YX, 01YW, 097N, 090N, 00HP, 00HQ and 094S
(blueprint: lem-pur-finite-etale-surjective-limit-cover).

Proof plan:
1. Every tower map is finite by cancellation against the finite structure maps, hence
   affine. Reindex along `ULift ℕ` and apply `lem-weil-pbc-limit-affine-transition`
   (`exists_limit_affine_transition_core`); `Over.forget X` creates this connected limit.
   The first projection is affine, so the structure map to `X` is affine.
2. On an affine open `U`, the base-changed stages are affine with finite étale coordinate
   ring maps (`Scheme.Hom.finite_appTop`, `HasRingHomProperty.appTop`;
   `lem-weil-pbc-etale-scheme-base-change`).
3. `Over.pullback U.ι` and `Over.forget` preserve the limit; `Γ` of the affine limit is the
   ring colimit, and `isoSpec` naturality gives the chart isomorphism with its projection
   and `FiniteEtaleTower.baseMap` equations.
4. The base-changed cone is a pro-affine-étale presentation of the chart, hence weakly étale
   and flat by `lem-pur-pro-affine-etale-weakly-etale`.
5. Base-changed transitions stay surjective; by `lem-pur-sequential-spectrum-surjective`
   the spectrum of the ring colimit maps onto the first stage, so the chart maps onto `U`.
6. Flat and surjective `Spec (baseMap)` is faithfully flat
   (`def-weil-pbc-faithfully-flat-ring-map`, Mathlib `flat_and_surjective_SpecMap_iff`).
7. Target locality (`lemma-stability`) over the affine-open cover gives
   global weak étaleness and surjectivity; the affine, hence quasi-compact, weakly étale
   singleton is a small pro-étale cover (`definition-small-pro-etale-site--1`). No compactness or
   separation assumption on `X` is used.
-/
theorem exists_finiteEtale_surjective_limit_cover {X : Scheme.{u}}
    (D : ℕᵒᵖ ⥤ Over X)
    (hfinite : ∀ n : ℕ, IsFinite (D.obj (op n)).hom)
    (hetale : ∀ n : ℕ, Etale (D.obj (op n)).hom)
    (hsurjective : ∀ n : ℕ, Surjective (D.obj (op n)).hom)
    (htransitionFinite : ∀ n : ℕ,
      IsFinite (D.map (homOfLE (Nat.le_succ n)).op).left)
    (htransitionEtale : ∀ n : ℕ,
      Etale (D.map (homOfLE (Nat.le_succ n)).op).left)
    (htransitionSurjective : ∀ n : ℕ,
      Surjective (D.map (homOfLE (Nat.le_succ n)).op).left) :
    ∃ c : Cone D, Nonempty (IsLimit ((Over.forget X).mapCone c)) ∧
      IsAffineHom c.pt.hom ∧ Surjective c.pt.hom ∧
      (∃ hf : WeaklyEtale c.pt.hom,
        Presieve.singleton
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ c.pt.hom hf)
            (B := Scheme.ProEt.mk (𝟙 X)) c.pt.hom (Category.comp_id _)) ∈
          Scheme.ProEt.precoverage X (Scheme.ProEt.mk (𝟙 X))) ∧
      ∀ (U : X.Opens), IsAffineOpen U →
        (∀ n : ℕ, IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n))) ∧
        (∀ n : ℕ,
          (pullback.snd (D.obj (op n)).hom U.ι).appTop.hom.Finite ∧
          (pullback.snd (D.obj (op n)).hom U.ι).appTop.hom.Etale) ∧
        (FiniteEtaleTower.baseMap D U).hom.FaithfullyFlat ∧
        ∃ e : pullback c.pt.hom U.ι ≅ Spec (colimit (FiniteEtaleTower.ringDiagram D U)),
          (e.hom ≫ Spec.map (FiniteEtaleTower.baseMap D U) =
            pullback.snd c.pt.hom U.ι ≫ ΓSpec.adjunction.unit.app U.toScheme) ∧
          ∀ n : ℕ,
            e.hom ≫ Spec.map (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op n))) =
              ((Over.pullback U.ι).map (c.π.app (op n))).left ≫
                ΓSpec.adjunction.unit.app ((FiniteEtaleTower.affineDiagram D U).obj (op n)) := by
  classical
  have (n : ℕ) : IsFinite (D.obj (op n)).hom := hfinite n
  have (n : ℕ) : Etale (D.obj (op n)).hom := hetale n
  have (n : ℕ) : Surjective (D.obj (op n)).hom := hsurjective n
  have (n : ℕ) : IsFinite (D.map (homOfLE (Nat.le_succ n)).op).left :=
    htransitionFinite n
  have (n : ℕ) : Etale (D.map (homOfLE (Nat.le_succ n)).op).left :=
    htransitionEtale n
  obtain ⟨c, ⟨hc⟩, hca⟩ := exists_affine_cone D hfinite
  have : IsAffineHom c.pt.hom := hca
  have charts (U : X.Opens) (hU : IsAffineOpen U) :
      WeaklyEtale (pullback.snd c.pt.hom U.ι) ∧
      Surjective (pullback.snd c.pt.hom U.ι) ∧
      (∀ n : ℕ, IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n))) ∧
      (∀ n : ℕ,
        (pullback.snd (D.obj (op n)).hom U.ι).appTop.hom.Finite ∧
        (pullback.snd (D.obj (op n)).hom U.ι).appTop.hom.Etale) ∧
      (FiniteEtaleTower.baseMap D U).hom.FaithfullyFlat ∧
      ∃ e : pullback c.pt.hom U.ι ≅ Spec (colimit (FiniteEtaleTower.ringDiagram D U)),
        (e.hom ≫ Spec.map (FiniteEtaleTower.baseMap D U) =
          pullback.snd c.pt.hom U.ι ≫ ΓSpec.adjunction.unit.app U.toScheme) ∧
        ∀ n : ℕ,
          e.hom ≫ Spec.map (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op n))) =
            ((Over.pullback U.ι).map (c.π.app (op n))).left ≫
              ΓSpec.adjunction.unit.app ((FiniteEtaleTower.affineDiagram D U).obj (op n)) := by
    have : IsAffine U.toScheme := hU
    have ha (n : ℕ) : IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n)) :=
      isAffine_of_isAffineHom (pullback.snd (D.obj (op n)).hom U.ι)
    have hwe := chart_proEtale D c hc hetale U ha
    have : WeaklyEtale (pullback.snd c.pt.hom U.ι) := hwe
    obtain ⟨e, he⟩ := chart_comparison D c hc U ha
    have hb := chart_base_equation D c U e (he 0)
    have hi := chart_iota_surjective D htransitionSurjective U ha
    have hcomp : Surjective (e.hom ≫ Spec.map
        (colimit.ι (FiniteEtaleTower.ringDiagram D U) (op (op 0)))) := inferInstance
    rw [he 0] at hcomp
    have : IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op 0)) := ha 0
    have : Surjective (((Over.pullback U.ι).map (c.π.app (op 0))).left) :=
      (MorphismProperty.cancel_right_of_respectsIso @Surjective _
        (ΓSpec.adjunction.unit.app
          ((FiniteEtaleTower.affineDiagram D U).obj (op 0)))).mp hcomp
    have hp : ((Over.pullback U.ι).map (c.π.app (op 0))).left ≫
        pullback.snd (D.obj (op 0)).hom U.ι = pullback.snd c.pt.hom U.ι :=
      ((Over.pullback U.ι).map (c.π.app (op 0))).w
    have hs : Surjective (pullback.snd c.pt.hom U.ι) := by
      rw [← hp]
      infer_instance
    have : Surjective (pullback.snd c.pt.hom U.ι) := hs
    have hf : Flat (Spec.map (FiniteEtaleTower.baseMap D U)) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @Flat e.hom, hb]
      infer_instance
    have hsurj : Surjective (Spec.map (FiniteEtaleTower.baseMap D U)) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective e.hom, hb]
      infer_instance
    refine ⟨hwe, hs, ha, ?_, (flat_and_surjective_SpecMap_iff _).mp ⟨hf, hsurj⟩,
      e, hb, he⟩
    intro n
    have : IsAffine ((FiniteEtaleTower.affineDiagram D U).obj (op n)) := ha n
    exact ⟨Scheme.Hom.finite_appTop _, HasRingHomProperty.appTop (P := @Etale) _
      inferInstance⟩
  let A := X.openCoverOfIsOpenCover (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X)
  have hwe : WeaklyEtale c.pt.hom := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @WeaklyEtale) A
    intro U
    exact (charts U.1 U.2).1
  have hs : Surjective c.pt.hom := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @Surjective) A
    intro U
    exact (charts U.1 U.2).2.1
  have : WeaklyEtale c.pt.hom := hwe
  have : Surjective c.pt.hom := hs
  refine ⟨c, ⟨hc⟩, hca, hs, ⟨hwe, ?_⟩, fun U hU ↦ (charts U hU).2.2⟩
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton]
  change Presieve.singleton c.pt.hom ∈ Scheme.proetalePrecoverage X
  exact Scheme.Hom.singleton_mem_propQCPrecoverage hwe

end AlgebraicGeometry
