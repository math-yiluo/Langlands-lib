/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift

/-! # Local representatives of positive-rank finite free stalk maps

We specialize the proved finite-family matrix lifting theorem to the top open
and a singleton family. The private comparison lemma below generalizes isomorphism conjugation to
intertwining by arbitrary natural transformations: naturality on free inclusions
reduces the comparison to a common central scalar.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation between free-preserving functors intertwines every
map between normalized free objects. Unlike conjugation invariance, this also
applies to noninvertible transformations. Naturality on free inclusions gives
one common scalar; its centrality gives the intertwining identity. -/
private lemma free_comparison_intertwines {X Z : Scheme.{u}}
    (F G : X.Modules ⥤ Z.Modules) (e : F ⟶ G)
    (a₀ : F.obj (Modules.unit X) ≅ Modules.unit Z)
    (b₀ : G.obj (Modules.unit X) ≅ Modules.unit Z)
    (a : ∀ K : Type u, F.obj (SheafOfModules.free K) ≅ SheafOfModules.free K)
    (b : ∀ K : Type u, G.obj (SheafOfModules.free K) ≅ SheafOfModules.free K)
    (ha : ∀ (K : Type u) (i : K), F.map (SheafOfModules.ιFree i) ≫ (a K).hom =
      a₀.hom ≫ SheafOfModules.ιFree i)
    (hb : ∀ (K : Type u) (i : K), G.map (SheafOfModules.ιFree i) ≫ (b K).hom =
      b₀.hom ≫ SheafOfModules.ιFree i)
    {I J : Type u} [Finite J]
    (f : SheafOfModules.free (R := Z.ringCatSheaf) I ⟶ SheafOfModules.free J) :
    ((a I).inv ≫ e.app _ ≫ (b I).hom) ≫ f =
      f ≫ (a J).inv ≫ e.app _ ≫ (b J).hom := by
  classical
  let := Fintype.ofFinite J
  let c (K : Type u) := (a K).inv ≫ e.app (SheafOfModules.free K) ≫ (b K).hom
  let c₀ := a₀.inv ≫ e.app (Modules.unit X) ≫ b₀.hom
  have hι (K : Type u) (i : K) :
      SheafOfModules.ιFree i ≫ c K = c₀ ≫ SheafOfModules.ιFree i := by
    have hai : SheafOfModules.ιFree i ≫ (a K).inv =
        a₀.inv ≫ F.map (SheafOfModules.ιFree i) := by
      rw [Iso.comp_inv_eq, Category.assoc, ha, Iso.inv_hom_id_assoc]
    dsimp only [c, c₀]
    rw [reassoc_of% hai, e.naturality_assoc, hb]
    simp only [Category.assoc]
  have hπ (j : J) : c J ≫ freeπ j = freeπ j ≫ c₀ := by
    apply free_hom_ext
    intro k
    rw [← Category.assoc, hι J k, Category.assoc, ιFree_freeπ,
      ← Category.assoc, ιFree_freeπ]
    split_ifs <;> simp
  change c I ≫ f = f ≫ c J
  apply free_hom_ext
  intro i
  rw [← Category.comp_id (SheafOfModules.ιFree i ≫ (c I ≫ f)),
    ← Category.comp_id (SheafOfModules.ιFree i ≫ (f ≫ c J)), ← sum_freeπ_ιFree]
  simp only [Preadditive.comp_sum, ← Category.assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Category.assoc]
  rw [reassoc_of% (hι I i), hπ j]
  -- At each open, both composites multiply by the same two ring elements.
  apply Modules.hom_ext
  intro U
  ext x
  let d := SheafOfModules.ιFree i ≫ f ≫ freeπ j
  change Hom.app d U (Hom.app c₀ U x) = Hom.app c₀ U (Hom.app d U x)
  let c₁ : Γ(Z, U) := Hom.app c₀ U (1 : Γ(Z, U))
  let d₁ : Γ(Z, U) := Hom.app d U (1 : Γ(Z, U))
  have hc (z : Γ(Z, U)) : (Hom.app c₀ U z : Γ(Z, U)) = z * c₁ := by
    simpa only [smul_eq_mul, mul_one] using Hom.app_smul c₀ (U := U) z (1 : Γ(Z, U))
  have hd (z : Γ(Z, U)) : (Hom.app d U z : Γ(Z, U)) = z * d₁ := by
    simpa only [smul_eq_mul, mul_one] using Hom.app_smul d (U := U) z (1 : Γ(Z, U))
  rw [hc, hd, hd, hc]
  simp only [mul_assoc, mul_comm c₁]


set_option maxRecDepth 2048 in
/-- Positive-rank finite-free stalk maps admit local representatives.
Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2.
Proof: Restrict first to the top open V and identify the restricted standard
free sheaves with standard free sheaves on V. Transport t by these free
isomorphisms and the restriction-stalk comparison. Apply
exists_finite_free_matrices_of_stalk_local to the singleton family containing
this transported map. Transport the resulting map back to restrictions of
the original free sheaves using restrictFunctorComp and restrictFunctorCongr.
Naturality of the within-open stalk comparison proves the desired equation
for the transported comparison E'. For the specified comparison E, consider
the natural automorphism E'.symm followed by E of stalk pullback. Naturality
on the free inclusions shows its normalized free components act on each
summand by the same endomorphism of the unit sheaf. Unit endomorphisms act
by multiplication by global functions, so this scalar commutes with every
finite matrix. Thus its conjugation fixes t. Cancel E' to identify the two
conjugations and obtain the equation for exactly the comparison in the statement.
(blueprint: lem-pc-finite-free-stalk-map-local-positive) -/
theorem exists_local_free_stalk_map_of_nonempty
    {Y : Scheme.{u}} (r s : ℕ) (y : Y)
    (hr : Nonempty (Fin r)) (hs : Nonempty (Fin s))
    (t : (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))),
      let E := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι)
          (Modules.pullback (U.fromSpecStalkOfMem y hyU)) ≪≫
        pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
        pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        E.hom.app _ ≫ t ≫ E.inv.app _ := by
  classical
  have : Nonempty (Fin r) := hr
  have : Nonempty (Fin s) := hs
  let V : Y.Opens := ⊤
  have hyV : y ∈ V := trivial
  let T := pullback (Y.fromSpecStalk y)
  let R₀ := restrictFunctor V.ι
  let S₀ := pullback (V.fromSpecStalkOfMem y hyV)
  let E₀ := Functor.isoWhiskerRight (restrictFunctorIsoPullback V.ι) S₀ ≪≫
    pullbackComp (V.fromSpecStalkOfMem y hyV) V.ι ≪≫
    pullbackCongr (V.fromSpecStalkOfMem_ι y hyV)
  let d (K : Type u) := restrictFreeIso V.ι K
  let f := S₀.map (d (ULift.{u} (Fin r))).inv ≫ E₀.hom.app _ ≫ t ≫
    E₀.inv.app _ ≫ S₀.map (d (ULift.{u} (Fin s))).hom
  obtain ⟨U, hUV, hyU, g, hg⟩ := exists_finite_free_matrices_of_stalk_local
    (ι := Unit) y V hyV (fun _ ↦ r) (fun _ ↦ s) (fun _ ↦ f)
  let R := restrictFunctor (Y.homOfLE hUV)
  let S := pullback (U.fromSpecStalkOfMem y hyU)
  let C := (restrictFunctorCongr (Y.homOfLE_ι hUV)).symm ≪≫
    restrictFunctorComp (Y.homOfLE hUV) V.ι
  let H := stalkRestrictionWithinIso y V hyV U hUV hyU
  let E' := Functor.isoWhiskerRight C S ≪≫ Functor.associator R₀ R S ≪≫
    Functor.isoWhiskerLeft R₀ H ≪≫ E₀
  let g' := C.hom.app _ ≫ R.map (d (ULift.{u} (Fin r))).hom ≫ g () ≫
    R.map (d (ULift.{u} (Fin s))).inv ≫ C.inv.app _
  refine ⟨U, hyU, g', ?_⟩
  let E := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) S ≪≫
    pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
    pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
  have hg' : S.map g' = E'.hom.app _ ≫ t ≫ E'.inv.app _ := by
    dsimp only [g']
    simp only [Functor.map_comp]
    have hg₀ : S.map (g ()) = H.hom.app _ ≫ f ≫ H.inv.app _ := hg ()
    rw [hg₀]
    dsimp only [f]
    simp only [Category.assoc, ← Functor.comp_map]
    rw [H.hom.naturality_assoc]
    rw [← H.inv.naturality_assoc]
    simp only [Functor.comp_obj, NatTrans.naturality_assoc, Functor.comp_map,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_map, CategoryTheory.Functor.map_id, Category.id_comp,
      cancelIso, Functor.isoWhiskerRight, Functor.isoWhiskerLeft, Iso.trans_hom,
      Functor.mapIso_hom, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
      Functor.associator_inv_app, E', R₀]
    erw [Category.id_comp]
  have he : E'.hom.app _ ≫ t ≫ E'.inv.app _ =
      E.hom.app _ ≫ t ≫ E.inv.app _ := by
    let D := E'.symm ≪≫ E
    have hD : D.hom.app _ ≫ t ≫ D.inv.app _ = t := by
      apply (cancel_epi (pullbackFreeIso (Y.fromSpecStalk y)
        (ULift.{u} (Fin r))).inv).mp
      apply (cancel_mono (pullbackFreeIso (Y.fromSpecStalk y)
        (ULift.{u} (Fin s))).hom).mp
      have hc := free_comparison_intertwines T T D.hom
        (pullbackObjUnitIso (Y.fromSpecStalk y))
        (pullbackObjUnitIso (Y.fromSpecStalk y))
        (pullbackFreeIso (Y.fromSpecStalk y)) (pullbackFreeIso (Y.fromSpecStalk y))
        (fun _ i ↦ pullback_map_ιFree_pullbackFreeIso_hom _ i)
        (fun _ i ↦ pullback_map_ιFree_pullbackFreeIso_hom _ i)
        ((pullbackFreeIso (Y.fromSpecStalk y) (ULift.{u} (Fin r))).inv ≫ t ≫
          (pullbackFreeIso (Y.fromSpecStalk y) (ULift.{u} (Fin s))).hom)
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ (pullbackFreeIso (Y.fromSpecStalk y)
          (ULift.{u} (Fin s))).inv ≫ D.inv.app _ ≫
          (pullbackFreeIso (Y.fromSpecStalk y) (ULift.{u} (Fin s))).hom) hc
    apply (cancel_epi (E'.inv.app _)).mp
    apply (cancel_mono (E'.hom.app _)).mp
    simpa [D, Category.assoc] using hD.symm
  exact hg'.trans he
end AlgebraicGeometry.Scheme.Modules
