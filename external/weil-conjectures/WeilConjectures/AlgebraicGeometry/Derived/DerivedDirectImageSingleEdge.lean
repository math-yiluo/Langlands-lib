/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleAdjunctionTranspose
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Single-complex normalization of the truncated counit
Source: Stacks Project, cohomology.tex, Tag 079W; derived.tex, Tags 08J5 and 06XS.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

-- Keep tensor/sheafification and derived-localization data behind their functor APIs.
attribute [local irreducible] Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackMap
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem transpose_top_naturality
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (L : D ⥤ E) (R : E ⥤ D) (l : A ⥤ B) (r : B ⥤ A)
    (adj : L ⊣ R) (a : l ⊣ r) (H : D ⥤ A) (H' : E ⥤ B)
    {C P : D} {K : E} (f : C ⟶ P) (d : L.obj P ⟶ K)
    (κ : H'.obj (L.obj C) ⟶ l.obj (H.obj C))
    (κ' : H'.obj (L.obj P) ⟶ l.obj (H.obj P)) [IsIso κ] [IsIso κ']
    (hκ : H'.map (L.map f) ≫ κ' = κ ≫ l.map (H.map f)) :
    a.homEquiv _ _ (inv κ ≫ H'.map ((adj.homEquiv _ _).symm
        (f ≫ adj.homEquiv _ _ d))) =
      H.map f ≫ a.homEquiv _ _ (inv κ' ≫ H'.map d) := by
  have hi : inv κ ≫ H'.map (L.map f) = l.map (H.map f) ≫ inv κ' := by
    apply (cancel_mono κ').1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc] using congrArg (fun z ↦ inv κ ≫ z) hκ
  rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, H'.map_comp]
  rw [← Category.assoc, hi, Category.assoc, a.homEquiv_naturality_left]

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

private theorem truncatedCounit_source {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE q)
    (K : schemeDerivedCategory T) (d : (derivedPullback g).obj C ⟶ K) :
    let adj := @pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
    let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        (adj.homEquiv C K d) ≫ topEdgeTruncatedCounit g q K =
      a.homEquiv _ _ (topEdgePullbackInverse g q C hC ≫
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map d) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let P := (t.truncLE q).obj ((schemeDerivedDirectImage g).obj K)
  let i := (t.truncLEι q).app ((schemeDerivedDirectImage g).obj K)
  let adj := @pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let d₀ := (adj.homEquiv P K).symm i
  have hP : P.IsLE q := by dsimp [P]; infer_instance
  have hi : IsIso (HS.map i) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (q + 1) q (by omega)
  have := hC
  let f := t.liftTruncLE (adj.homEquiv C K d) q
  have hf : f ≫ i = adj.homEquiv C K d := t.liftTruncLE_ι _ q
  have hn := (derivedPullback_topCohomology g q C hC).choose_spec.2.2.1 P hP f
  have := (derivedPullback_topCohomology g q C hC).choose_spec.2.1
  have := (derivedPullback_topCohomology g q P hP).choose_spec.2.1
  have hh := transpose_top_naturality (derivedPullback g) (schemeDerivedDirectImage g)
    (Scheme.Modules.tensorPullback g) (Scheme.Modules.pushforward g) adj a HS HT f d₀
    (derivedPullbackTopCohomology g q C hC)
    (derivedPullbackTopCohomology g q P hP) hn
  have hfd : f ≫ adj.homEquiv P K d₀ = adj.homEquiv C K d := by
    simpa only [d₀, Equiv.apply_symm_apply] using hf
  rw [hfd, Equiv.symm_apply_apply] at hh
  change HS.map (adj.homEquiv C K d) ≫ topEdgeTruncatedCounit g q K =
    a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q C hC) ≫ HT.map d)
  rw [hh, ← hf, HS.map_comp]
  change (HS.map f ≫ HS.map i) ≫ (inv (HS.map i) ≫
      a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q P hP) ≫ HT.map d₀)) =
    HS.map f ≫ a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q P hP) ≫ HT.map d₀)
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem topProjection_single {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (q : ℤ) (N : A) :
    derivedTopTruncationProjection q ((DerivedCategory.singleFunctor A q).obj N)
        (by infer_instance) =
      (DerivedCategory.singleFunctor A q).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A q).inv.app N) := by
  let C := (DerivedCategory.singleFunctor A q).obj N
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso A q
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE q).1
  dsimp only
  have h : (DerivedCategory.homologyFunctor A q).map
      (derivedTopTruncationProjection q C (by infer_instance)) = E.inv.app _ := by
    exact (Equiv.ofBijective _
      (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE q)).apply_symm_apply _
  change (DerivedCategory.homologyFunctor A q).map
    (derivedTopTruncationProjection q C (by infer_instance)) = _
  rw [h]
  apply (cancel_epi (E.inv.app N)).1
  simpa only [C, E, Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] using
    E.inv.naturality (E.inv.app N)

-- Keep the top comparison as a composite of functor maps and single isomorphisms.
private theorem single_kappa {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (N : SheafOfModules.{u} (moduleRings S.toRingedSpace)) :
    derivedPullbackTopCohomology g q ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj N) (by infer_instance) ≫
      (Scheme.Modules.tensorPullback g).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).hom.app N) =
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map
        (pinnedModulePullbackComparisonAt g q N) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).hom.app
          ((Scheme.Modules.tensorPullback g).obj N) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let L := derivedPullback g
  let l : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let SS := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let ST := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let ES := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let ET := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let a := ES.inv.app N
  have hn : L.map (SS.map a) ≫ pinnedModulePullbackComparisonAt g q (HS.obj (SS.obj N)) =
      pinnedModulePullbackComparisonAt g q N ≫ ST.map (l.map a) := by
    unfold pinnedModulePullbackComparisonAt derivedSingleComparisonOfCounit
    simp only [cast_eq]
    rw [← Category.assoc]
    have h := (@pinnedPullbackCounit.{u, w} _
      (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g).naturality
        ((HomotopyCategory.singleFunctor _ q).map a)
    change L.map (SS.map a) ≫ _ = _ at h
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at h
    rw [h]
    simp only [Category.assoc]
    apply congrArg (fun z ↦ _ ≫ z)
    change DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((l.mapHomologicalComplex (.up ℤ)).map
            ((CochainComplex.singleFunctor _ q).map a))) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex l (.up ℤ) q).hom.app _)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex l (.up ℤ) q).hom.app N)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((CochainComplex.singleFunctor _ q).map (l.map a)))
    simp only [← Functor.map_comp]
    exact congrArg (fun f ↦ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)).map f))
      ((HomologicalComplex.singleMapHomologicalComplex l (.up ℤ) q).hom.naturality a)
  unfold derivedPullbackTopCohomology
  rw [topProjection_single]
  change (HT.map (L.map (SS.map a)) ≫
      HT.map (pinnedModulePullbackComparisonAt g q (HS.obj (SS.obj N))) ≫
      ET.hom.app _) ≫ l.map (ES.hom.app N) = _
  rw [← Category.assoc (HT.map (L.map (SS.map a))), ← HT.map_comp, hn, HT.map_comp]
  have he := ET.hom.naturality (l.map a)
  change HT.map (ST.map (l.map a)) ≫ ET.hom.app _ = ET.hom.app _ ≫ l.map a at he
  simp only [Category.assoc]
  rw [reassoc_of% he, ← l.map_comp, ES.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  rw [l.map_id]
  exact congrArg (fun z ↦ HT.map (pinnedModulePullbackComparisonAt g q N) ≫ z)
    (Category.comp_id (ET.hom.app (l.obj N)))

/-- On a single complex the truncated counit is normalized by the derived unit.
Source: Stacks Project, cohomology.tex, Tag 079W (normalized adjunction);
derived.tex, Tags 08J5 and 06XS (truncation and the shifted heart).
(blueprint: lem-weil-pbc-single-truncated-counit-normalization).

Proof: Put P = tau_{<=q} Rg_*(M[-q]). The target of the truncated counit is a
single complex in degree q. Since Lg*P is at most q, the homology Hom-bijection identifies
its derived counit with the single of its degree-q map after the top projection.
Transpose this equality using the normalization of exists_schemeDerivedAdjunction at
the single complex in degree q. The termwise single adjunction sends the tensor-pullback
comparison followed by a module map to the single ordinary transpose followed by the
right-derived unit. The definition of kappa uses this same pinned left-derived counit.
Thus applying degree-q homology and cancelling the invertible homology of P's inclusion
gives precisely the displayed equation. The ordinary adjunction is the tensor adjunction
selected by exists_tensorPullbackAdjunction. All comparisons use the same q, so there is
no independently chosen shift sign. Zero modules and empty schemes obey the same unit
and kernel identities. -/
theorem topEdgeSingleDirectImageMap_counit {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
    let ES := DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
    let ET := DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
    HS.map (topEdgeSingleDirectImageMap g q M) ≫
          topEdgeTruncatedCounit g q ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) =
        ES.hom.app ((Scheme.Modules.pushforward g).obj M) ≫
          (Scheme.Modules.pushforward g).map (ET.inv.app M) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let SS := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let ST := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let ES := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let ET := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let l : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
  let r : SheafOfModules.{u} (moduleRings T.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings S.toRingedSpace) := Scheme.Modules.pushforward g
  let a : l ⊣ r := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let adj := @pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
  let c := pinnedModulePullbackComparisonAt g q (r.obj M)
  let d := c ≫ ST.map (a.counit.app M)
  have hac : a.homEquiv (r.obj M) M (a.counit.app M) = 𝟙 (r.obj M) := by
    rw [← a.homEquiv_symm_id]
    exact (a.homEquiv (r.obj M) M).apply_symm_apply _
  have hd : adj.homEquiv (SS.obj (r.obj M)) (ST.obj M) d =
      topEdgeSingleDirectImageMap g q M := by
    have h := topEdgeSingleAdjunctionTranspose g q (r.obj M) M (a.counit.app M)
    change adj.homEquiv (SS.obj (r.obj M)) (ST.obj M) d =
      SS.map (a.homEquiv (r.obj M) M (a.counit.app M)) ≫ _ at h
    simpa only [hac, SS.map_id, Category.id_comp] using h
  have hκ := (derivedPullback_topCohomology g q (SS.obj (r.obj M))
    (by infer_instance)).choose_spec.2.1
  let κ := derivedPullbackTopCohomology g q (SS.obj (r.obj M)) (by infer_instance)
  have hm : inv κ ≫ HT.map d ≫ ET.hom.app M =
      l.map (ES.hom.app (r.obj M)) ≫ a.counit.app M := by
    apply (cancel_epi κ).1
    simp only [IsIso.hom_inv_id_assoc]
    change HT.map (c ≫ ST.map (a.counit.app M)) ≫ ET.hom.app M =
      (κ ≫ l.map (ES.hom.app (r.obj M))) ≫ a.counit.app M
    have hk := single_kappa g q (r.obj M)
    change κ ≫ l.map (ES.hom.app (r.obj M)) = HT.map c ≫ ET.hom.app _ at hk
    rw [hk, HT.map_comp, Category.assoc, Category.assoc]
    have hn := ET.hom.naturality (a.counit.app M)
    exact congrArg (fun z ↦ HT.map c ≫ z) hn
  have ha : a.homEquiv _ _ (inv κ ≫ HT.map d) =
      ES.hom.app (r.obj M) ≫ r.map (ET.inv.app M) := by
    apply (cancel_mono (r.map (ET.hom.app M))).1
    rw [← a.homEquiv_naturality_right, Category.assoc, hm,
      a.homEquiv_naturality_left]
    dsimp only [Functor.id_obj]
    rw [hac]
    simp only [Category.comp_id, Category.assoc, ← r.map_comp, ET.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [r.map_id, Category.comp_id]
  have h := truncatedCounit_source g q (SS.obj (r.obj M)) (by infer_instance) (ST.obj M) d
  change HS.map (adj.homEquiv (SS.obj (r.obj M)) (ST.obj M) d) ≫
    topEdgeTruncatedCounit g q (ST.obj M) =
      a.homEquiv _ _ (inv κ ≫ HT.map d) at h
  rw [hd] at h
  exact h.trans ha

end AlgebraicGeometry
