/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Basis
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Transposed entries for sheafified dual basis maps

Source: Stacks Project, schemes.tex, Tag 01HV, functoriality of localization;
Mathlib LinearAlgebra/Dual/Basis.lean, Basis.dualBasis_repr.
(blueprint: lem-sc-affine-basis-dual-matrix).
-/

@[expose] public section

universe u
open CategoryTheory Module
namespace AlgebraicGeometry

/-- The based affine module in free-sheaf coordinates.
Source: Stacks Project, Tag 01HV.
(blueprint: lem-sc-affine-basis-dual-matrix). -/
@[irreducible]
noncomputable def affineBasisCoordinatesIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} (b : Basis I Γ(Y, U.1) M) :
    (((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M) :
      SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
    ((tilde.functor Γ(Y, U.1)).mapIso b.repr.toModuleIso ≪≫
      tildeFinsupp (R := Γ(Y, U.1)) I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

/-- The algebraic module dual in dual-basis free-sheaf coordinates.
Source: Stacks Project, Tag 01HV; Basis.dualBasis_repr.
(blueprint: lem-sc-affine-basis-dual-matrix). -/
@[irreducible]
noncomputable def affineDualBasisCoordinatesIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Finite I]
    (b : Basis I Γ(Y, U.1) M) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) :
        SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I := by
  classical
  exact (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
    ((tilde.functor Γ(Y, U.1)).mapIso
      ((ModuleCat.homLinearEquiv.trans b.dualBasis.repr).toModuleIso) ≪≫
        tildeFinsupp (R := Γ(Y, U.1)) I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

set_option backward.isDefEq.respectTransparency.types false in
private lemma tilde_single {R : CommRingCat.{u}} {I : Type u} (i : I) :
    (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i)) ≫
      (tildeFinsupp (R := R) I).hom = SheafOfModules.ιFree i := by
  let H : Limits.IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    Limits.isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun _ : I ↦ ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ ↦ SheafOfModules.unit.{u} (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ ↦ tildeSelf)
  have h := Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((Limits.IsColimit.precomposeHomEquiv e.symm _).symm H)
    (Limits.coproductIsCoproduct _) (Discrete.mk i)
  change (𝟙 _ ≫ (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i))) ≫
    (tildeFinsupp (R := R) I).hom = SheafOfModules.ιFree i at h
  simpa only [Category.id_comp] using h

set_option backward.isDefEq.respectTransparency.types false in
private lemma restrict_free_single {X Z : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] {I : Type u} (i : I) :
    (Scheme.Modules.restrictFunctor g).map (SheafOfModules.ιFree i) ≫
        (Scheme.Modules.restrictFreeIso g I).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback g).app
        (SheafOfModules.unit X.ringCatSheaf) ≪≫
          Scheme.Modules.pullbackObjUnitIso g).hom ≫ SheafOfModules.ιFree i := by
  dsimp only [Scheme.Modules.restrictFreeIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, NatTrans.naturality]
  simp only [Category.assoc, Scheme.Modules.pullback_map_ιFree_pullbackFreeIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[irreducible]
private noncomputable def affineFreeIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (I : Type u) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (I →₀ Γ(Y, U.1)))) ≅
        SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso (tildeFinsupp I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

set_option backward.isDefEq.respectTransparency.types false in
@[irreducible]
private noncomputable def affineUnitIso {Y : Scheme.{u}} (U : Y.affineOpens) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) ≅
        SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback U.2.isoSpec.hom).app _ ≪≫
    Scheme.Modules.pullbackObjUnitIso U.2.isoSpec.hom

set_option backward.isDefEq.respectTransparency.types false in
private lemma affine_free_single {Y : Scheme.{u}} (U : Y.affineOpens)
    {I : Type u} (i : I) :
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).map
      (ModuleCat.ofHom (Finsupp.lsingle i)) ≫ (affineFreeIso U I).hom =
        (affineUnitIso U).hom ≫ SheafOfModules.ιFree i := by
  unfold affineFreeIso affineUnitIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
  rw [← Functor.map_comp_assoc, tilde_single (R := Γ(Y, U.1)) i,
    restrict_free_single U.2.isoSpec.hom i]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private lemma free_component {R : CommRingCat.{u}} {X : Scheme.{u}}
    (T : ModuleCat.{u} R ⥤ SheafOfModules.{u} X.ringCatSheaf) [T.Additive]
    (e : ∀ K : Type u, T.obj (ModuleCat.of R (K →₀ R)) ≅ SheafOfModules.free K)
    (e₀ : T.obj (ModuleCat.of R R) ≅ SheafOfModules.unit X.ringCatSheaf)
    (hι : ∀ (K : Type u) (k : K),
      T.map (ModuleCat.ofHom (Finsupp.lsingle k)) ≫ (e K).hom =
        e₀.hom ≫ SheafOfModules.ιFree k)
    {A B : ModuleCat.{u} R} {I J : Type u} [DecidableEq J]
    (p : A ≅ ModuleCat.of R (I →₀ R)) (q : B ≅ ModuleCat.of R (J →₀ R))
    (f : A ⟶ B) (i : I) (j : J) :
    SheafOfModules.ιFree i ≫ (T.mapIso p ≪≫ e I).inv ≫ T.map f ≫
      (T.mapIso q ≪≫ e J).hom ≫ Scheme.Modules.freeπ j =
    e₀.inv ≫ T.map (ModuleCat.ofHom (Finsupp.lsingle i) ≫ p.inv ≫ f ≫ q.hom ≫
      ModuleCat.ofHom (Finsupp.lapply j)) ≫ e₀.hom := by
  have hinv (K : Type u) (k : K) : SheafOfModules.ιFree k ≫ (e K).inv =
      e₀.inv ≫ T.map (ModuleCat.ofHom (Finsupp.lsingle k)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hι, Iso.inv_hom_id_assoc]
  have hπ : (e J).hom ≫ Scheme.Modules.freeπ j =
      T.map (ModuleCat.ofHom (Finsupp.lapply j)) ≫ e₀.hom := by
    rw [← cancel_epi (e J).inv, Iso.inv_hom_id_assoc]
    apply Scheme.Modules.free_hom_ext
    intro k
    rw [reassoc_of% (hinv J k), ← T.map_comp_assoc]
    have h : ModuleCat.ofHom (Finsupp.lsingle k (R := R) (M := R)) ≫
        ModuleCat.ofHom (Finsupp.lapply j) =
        if k = j then 𝟙 _ else 0 := by
      split_ifs with h
      · subst k
        ext
        simp
      · ext
        simp [h]
    rw [h, Scheme.Modules.ιFree_freeπ]
    split_ifs <;> simp
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% (hinv I i), hπ]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Sheafification and restriction preserve the transposed entries of a dual map.
Source: Stacks Project, schemes.tex, Tag 01HV(4)-(5) and functoriality;
Basis.dualBasis_repr in Mathlib.LinearAlgebra.Dual.Basis.
(blueprint: lem-sc-affine-basis-dual-matrix).

Proof: Write a_ij = bM.repr (f (bN j)) i. The coefficient at j of the functional
bM.dualBasis i precomposed with f is a_ij, by dualBasis_repr. The basis repr
maps and their inverses therefore identify the two algebraic matrix components
with the same scalar endomorphism of A. The coproduct comparison tildeFinsupp
carries each sheafified single basis vector to the corresponding free generator:
this follows from its defining coconePointUniqueUpToIso and the injection
identities for that isomorphism. Its coordinate projections likewise agree by
finite coproduct extensionality. The restrictFreeIso has the same property,
by the generator identities for mapFreeIso and the natural isomorphism between
restriction and pullback. Apply the two functors to the equal scalar components;
functors preserve their compositions, so the displayed components are equal.
This proves the assertion on all opens without any choice of sections. The
argument uses no division or nonzero coefficient. For an empty basis there
are no pairs (i,j), and for a zero ring all scalar components are zero. -/
theorem affineBasisDualMatrix_component {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) {I J : Type u} [Finite I] [Finite J]
    [DecidableEq I] [DecidableEq J]
    (bM : Basis I Γ(Y, U.1) M) (bN : Basis J Γ(Y, U.1) N) (f : N ⟶ M)
    (i : I) (j : J) :
    let S := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let T := tilde.functor Γ(Y, U.1) ⋙ S
    let eM := affineBasisCoordinatesIso U M bM
    let eN := affineBasisCoordinatesIso U N bN
    let dM := affineDualBasisCoordinatesIso U M bM
    let dN := affineDualBasisCoordinatesIso U N bN
    SheafOfModules.ιFree i ≫ dM.inv ≫
        T.map (ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
          (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)) ≫ dN.hom ≫ Scheme.Modules.freeπ j =
      SheafOfModules.ιFree j ≫ eN.inv ≫ T.map f ≫ eM.hom ≫ Scheme.Modules.freeπ i :=
  by
    classical
    dsimp only
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    have : (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive :=
      Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback
        U.2.isoSpec.hom).symm
    let pM := bM.repr.toModuleIso
    let pN := bN.repr.toModuleIso
    let pdM : ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ≅
        ModuleCat.of Γ(Y, U.1) (I →₀ Γ(Y, U.1)) := by
      letI : DecidableEq I := Classical.typeDecidableEq I
      exact (ModuleCat.homLinearEquiv.trans bM.dualBasis.repr).toModuleIso
    let pdN : ModuleCat.of Γ(Y, U.1) (N ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ≅
        ModuleCat.of Γ(Y, U.1) (J →₀ Γ(Y, U.1)) := by
      letI : DecidableEq J := Classical.typeDecidableEq J
      exact (ModuleCat.homLinearEquiv.trans bN.dualBasis.repr).toModuleIso
    let df := ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
      (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)
    have halg : ModuleCat.ofHom (Finsupp.lsingle i) ≫ pdM.inv ≫ df ≫ pdN.hom ≫
        ModuleCat.ofHom (Finsupp.lapply j) =
      ModuleCat.ofHom (Finsupp.lsingle j) ≫ pN.inv ≫ f ≫ pM.hom ≫
        ModuleCat.ofHom (Finsupp.lapply i) := by
      ext
      simp [pM, pN, pdM, pdN, df, ModuleCat.homLinearEquiv]
      rfl
    have h := congrArg (fun g ↦ (affineUnitIso U).inv ≫ T.map g ≫
      (affineUnitIso U).hom) halg
    rw [← free_component (R := Γ(Y, U.1)) (X := U.1.toScheme)
        T (affineFreeIso U) (affineUnitIso U)
        (fun K k ↦ affine_free_single U k) pdM pdN df i j,
      ← free_component (R := Γ(Y, U.1)) (X := U.1.toScheme)
        T (affineFreeIso U) (affineUnitIso U)
        (fun K k ↦ affine_free_single U k) pN pM f j i] at h
    simpa only [pM, pN, pdM, pdN, df, T, affineBasisCoordinatesIso,
      affineDualBasisCoordinatesIso, affineFreeIso, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Functor.comp_map, Functor.map_comp,
      Category.assoc] using h

end AlgebraicGeometry
