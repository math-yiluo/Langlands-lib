/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexToSingle
public import WeilConjectures.Algebra.Homology.SignedModuleDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeDualNaturality
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Associated sheafification of finite free signed duals

Source: Stacks Project, duality.tex, Tag 0BQZ; schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-complex-comparison).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem signed_dual_iso_of_components
    {A : Type u} [CommRing A] {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (T : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (hT : T.Additive)
    (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (O : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (e0 : ∀ q : ℕ, SheafOfModules.homObj (R := R) (T.obj (K.X q)) O ≅
      T.obj (ModuleCat.of A (K.X q ⟶ ModuleCat.of A A)))
    (h0 : ∀ q : ℕ,
      SheafOfModules.homObjMap (R := R) (T.map (K.d (q + 1) q)) (𝟙 O) ≫
        (e0 (q + 1)).hom = (e0 q).hom ≫
          T.map (ModuleCat.ofHom (Linear.leftComp A (ModuleCat.of A A)
            (K.d (q + 1) q)))) :
    Nonempty (signedSheafDualComplex (R := R)
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)) O ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ModuleCat.signedDualCochainComplex K)) := by
  classical
  let L := K.extend ComplexShape.embeddingDownNat
  let B := CochainComplex.of
    (fun q ↦ ModuleCat.of A (K.X q ⟶ ModuleCat.of A A))
    (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
      Linear.leftComp A (ModuleCat.of A A) (K.d (q + 1) q)))
    (ModuleCat.signedDualBoundary_comp K)
  let D := B.extend ComplexShape.embeddingUpNat
  let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let F := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj D
  let H := (SheafOfModules.homFunctor R).flip.obj O
  let a (q : ℕ) : L.X (-(q : ℤ)) ≅ K.X q :=
    K.extendXIso ComplexShape.embeddingDownNat rfl
  let c (q : ℕ) : D.X (q : ℤ) ≅
      ModuleCat.of A (K.X q ⟶ ModuleCat.of A A) :=
    B.extendXIso ComplexShape.embeddingUpNat rfl
  let ep (q : ℕ) : (signedSheafDualComplex (R := R)
      E O).X (q : ℤ) ≅ F.X (q : ℤ) :=
    H.mapIso (T.mapIso (a q)).symm.op ≪≫
      e0 q ≪≫ T.mapIso (c q).symm
  have hz (n : ℤ) (hn : n < 0) :
      CategoryTheory.Limits.IsZero ((signedSheafDualComplex (R := R) E O).X n) := by
    have hL : CategoryTheory.Limits.IsZero (L.X (-n)) := K.isZero_extend_X _ _ (by
      intro q
      simp only [ComplexShape.embeddingDownNat_f]
      omega)
    exact H.map_isZero ((T.map_isZero hL).op)
  have hzF (n : ℤ) (hn : n < 0) : CategoryTheory.Limits.IsZero (F.X n) := by
    exact T.map_isZero (HomologicalComplex.isZero_extend_X _ _ _ (by
      intro q
      simp only [ComplexShape.embeddingUpNat_f]
      omega))
  let e (n : ℤ) :
      (signedSheafDualComplex (R := R) E O).X n ≅ F.X n :=
    match n with
    | .ofNat q => ep q
    | .negSucc q => (hz _ (by omega)).iso (hzF _ (by omega))
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro n m hnm
  have hm : m = n + 1 := hnm.symm
  subst m
  cases n with
  | negSucc q => exact (hz _ (by omega)).eq_of_src _ _
  | ofNat q =>
    simp only [e]
    change (ep q).hom ≫ F.d (q : ℤ) ((q : ℤ) + 1) =
      (signedSheafDualComplex (R := R) E O).d
        (q : ℤ) ((q : ℤ) + 1) ≫ (ep (q + 1)).hom
    let δ := ModuleCat.ofHom (Linear.leftComp A (ModuleCat.of A A) (K.d (q + 1) q))
    have hd : D.d (q : ℤ) ((q : ℤ) + 1) =
        (c q).hom ≫ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
          Linear.leftComp A (ModuleCat.of A A) (K.d (q + 1) q)) ≫ (c (q + 1)).inv := by
      simpa only [B, CochainComplex.of_d] using
        (B.extend_d_eq ComplexShape.embeddingUpNat
          (i := q) (j := q + 1) (i' := (q : ℤ)) (j' := (q : ℤ) + 1) rfl (by simp))
    have hl : L.d (-((q : ℤ) + 1)) (-(q : ℤ)) =
        (a (q + 1)).hom ≫ K.d (q + 1) q ≫ (a q).inv := by
      exact K.extend_d_eq ComplexShape.embeddingDownNat (by simp) rfl
    have hs : ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
        Linear.leftComp A (ModuleCat.of A A) (K.d (q + 1) q)) =
        (-(q : ℤ).negOnePow) • δ := by
      apply ModuleCat.hom_ext
      ext f x
      simp [δ, Units.smul_def, pow_succ,
        Linear.leftComp]
    have hdS : (signedSheafDualComplex (R := R) E O).d (q : ℤ) ((q : ℤ) + 1) =
        -(q : ℤ).negOnePow • SheafOfModules.homObjMap (R := R)
          (T.map (L.d (-((q : ℤ) + 1)) (-(q : ℤ)))) (𝟙 O) :=
      by
        simp only [signedSheafDualComplex, CochainComplex.of_d]
        rfl
    rw [hdS]
    change (ep q).hom ≫ T.map (D.d (q : ℤ) ((q : ℤ) + 1)) =
      (-(q : ℤ).negOnePow • SheafOfModules.homObjMap (R := R)
        (T.map (L.d (-((q : ℤ) + 1)) (-(q : ℤ)))) (𝟙 O)) ≫ (ep (q + 1)).hom
    rw [hd, hs, hl]
    dsimp only [ep, Iso.trans, Functor.mapIso, Iso.symm, Iso.op]
    simp only [Functor.map_comp, Functor.map_units_smul, Category.assoc]
    change (H.map (T.map (a q).inv).op ≫ (e0 q).hom ≫ T.map (c q).inv) ≫
        T.map (c q).hom ≫ (-(q : ℤ).negOnePow • T.map δ) ≫ T.map (c (q + 1)).inv =
      (-(q : ℤ).negOnePow • H.map
        (T.map (a (q + 1)).hom ≫ T.map (K.d (q + 1) q) ≫ T.map (a q).inv).op) ≫
        H.map (T.map (a (q + 1)).inv).op ≫ (e0 (q + 1)).hom ≫ T.map (c (q + 1)).inv
    simp only [op_comp, Functor.map_comp, Category.assoc,
      Linear.units_smul_comp, Linear.comp_units_smul, Iso.inv_hom_id_map_assoc]
    have ha : H.map (T.map (a (q + 1)).hom).op ≫
        H.map (T.map (a (q + 1)).inv).op = 𝟙 _ :=
      (H.mapIso (T.mapIso (a (q + 1))).op).hom_inv_id
    rw [← Category.assoc (H.map (T.map (a (q + 1)).hom).op)
      (H.map (T.map (a (q + 1)).inv).op) _, ha, Category.id_comp]
    have hn : H.map (T.map (K.d (q + 1) q)).op ≫ (e0 (q + 1)).hom =
        (e0 q).hom ≫ T.map δ := h0 q
    rw [← Category.assoc (H.map (T.map (K.d (q + 1) q)).op) (e0 (q + 1)).hom _, hn]
    erw [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sheafification and transport to an affine open commute with signed duals
of degreewise finite free chain complexes.

Source: Stacks Project, duality.tex, Tag 0BQZ, local finite free Hom computation;
schemes.tex, Tag 01HV, associated sheaves on affine schemes.
(blueprint: lem-sc-affine-finite-free-dual-complex-comparison).

Proof: choose finite bases of K_q. On each standard open D(g), the associated
sheaf has the localized basis. An internal sheaf map to the structure sheaf is
uniquely determined by its values on these basis sections. Consequently the
internal dual identifies with the associated sheaf of Hom_A(K_q,A). A change
of standard open localizes each value, so these coordinate identifications
commute with restrictions and glue to inverse sheaf maps. This description is
independent of the basis: it sends a functional to its localized evaluations.
For every boundary K_(q+1) → K_q, both induced maps are precomposition with
its localized matrix, so the degree identifications commute with boundaries.
Multiplication by -(-1)^q in the sheaf dual equals the sheafification of
multiplication by (-1)^(q+1) in the module dual. The extension isomorphisms
identify source cochain degree -q with K_q. Negative dual degrees have zero
objects on both sides, since the extended chain complex vanishes in positive
cochain degrees. Thus the degreewise maps give a complex isomorphism.
Transport along U.isoSpec is an equivalence and preserves all these maps.
There is no boundedness or regularity assumption: each degree is handled
separately, with no infinite sum. Rank zero terms, the zero ring and empty
charts use the unique maps between zero objects. -/
theorem affine_finite_free_dual_complex_comparison
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (K : ChainComplex (ModuleCat.{u} Γ(Y, U.1)) ℕ)
    (hfree : ∀ q : ℕ, Module.Free Γ(Y, U.1) (K.X q))
    (hfinite : ∀ q : ℕ, Module.Finite Γ(Y, U.1) (K.X q)) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)
    Nonempty (signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf) E
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ModuleCat.signedDualCochainComplex K)) := by
  classical
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  have : (tilde.functor Γ(Y, U.1)).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := Γ(Y, U.1)) f g
  have : (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive := ⟨by intros; rfl⟩
  have hT : T.Additive := inferInstanceAs
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive
  have (q : ℕ) : Module.Free Γ(Y, U.1) (K.X q) := hfree q
  have (q : ℕ) : Module.Finite Γ(Y, U.1) (K.X q) := hfinite q
  let b (q : ℕ) := Module.Free.chooseBasis Γ(Y, U.1) (K.X q)
  exact signed_dual_iso_of_components (R := U.1.toScheme.toRingedSpace.sheaf) T hT K
    (SheafOfModules.unit U.1.toScheme.ringCatSheaf)
    (fun q ↦ affineBasisDualIso U (K.X q) (b q))
    (fun q ↦ affineBasisDualIso_naturality U (K.X q) (K.X (q + 1))
      (b q) (b (q + 1)) (K.d (q + 1) q))

end AlgebraicGeometry
