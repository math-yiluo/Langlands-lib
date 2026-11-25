/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Positive-degree Zariski cohomology classes vanish locally

Source: Stacks Project, Etale Cohomology, Lemma 0GY0 (label `lemma-gabber-criterion`),
line 14228, proof (blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

private noncomputable abbrev freeAbelianSheaf (X : Scheme.{u}) : X.Opens ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf _ _

private noncomputable def sectionEquiv {X : Scheme.{u}} (U : X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((freeAbelianSheaf X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv
    _ F).trans (((AddCommGrpCat.adj.whiskerRight X.Opensᵒᵖ).homEquiv
      (yoneda.obj U) F.obj).trans yonedaEquiv)

private lemma sectionEquiv_comp {X : Scheme.{u}} (U : X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (freeAbelianSheaf X).obj U ⟶ F) (f : F ⟶ G) :
    sectionEquiv U G (a ≫ f) = f.hom.app (op U) (sectionEquiv U F a) := by
  simp only [sectionEquiv, Equiv.trans_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma sectionEquiv_map {X : Scheme.{u}} {U V : X.Opens} (f : U ⟶ V)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (freeAbelianSheaf X).obj V ⟶ F) :
    sectionEquiv U F ((freeAbelianSheaf X).map f ≫ a) =
      F.obj.map f.op (sectionEquiv V F a) := by
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight X.Opensᵒᵖ).homEquiv _ F.obj)
        (((sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).homEquiv _ F)
          ((presheafToSheaf _ _).map
            (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ a))) = _
  have h := (sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).homEquiv_naturality_left
      (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) a
  dsimp only [Functor.whiskeringRight] at *
  rw [h]
  have h' := (AddCommGrpCat.adj.whiskerRight X.Opensᵒᵖ).homEquiv_naturality_left
    (yoneda.map f)
    (((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv _ F) a)
  dsimp only [Functor.whiskeringRight, sheafToPresheaf, ObjectProperty.ι, inducedFunctor] at h'
  erw [h']
  exact (yonedaEquiv_naturality _ f).symm

private lemma sectionEquiv_zero {X : Scheme.{u}} (U : X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    sectionEquiv U F 0 = 0 := by
  have h := sectionEquiv_comp U (0 : (freeAbelianSheaf X).obj U ⟶ F) (0 : F ⟶ F)
  simpa using h

-- Comparing Ext and section cocycles elaborates several adjunctions and the derived category.
/-- Section cocycles of an injective resolution represent object cohomology, naturally
in the open, and section coboundaries represent zero.

Source: Stacks Project, Cohomology on Sites, Section 01FT and Lemma 01FW, proof
(blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).

Proof: For each open U, let A_U be the sheafification of the free abelian presheaf
on yoneda U. Sheafification, free-forgetful and Yoneda adjunctions identify
Hom(A_U, F) with F(U), naturally in both U and the abelian sheaf F. Applied to each
term and differential of I, this identifies Hom(A_U, I) with the section complex
I(U). Computing Ext(A_U, G, n+1) using I therefore gives the class map c_U on
section cocycles. Every class has a cocycle representative, since cohomology is
cycles modulo boundaries. Naturality of the adjunctions and the Ext computation
identifies restriction along f with the class of the restricted cocycle. Finally,
d(t) is a coboundary, so its class is zero. The proof arguments to c merely certify
membership in the kernel; proof irrelevance makes the map independent of them.
This comparison does not assert that any cocycle is locally a coboundary. -/
private theorem zariski_resolution_cocycle_classes {X : Scheme.{u}}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) :
    ∃ c : ∀ (U : X.Opens) (s : (I.cocomplex.X (n + 1)).obj.obj (op U)),
      (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) s = 0 →
        (G.cohomologyPresheaf (n + 1)).obj (op U),
      (∀ (U : X.Opens) (ξ : (G.cohomologyPresheaf (n + 1)).obj (op U)),
        ∃ s hs, c U s hs = ξ) ∧
      (∀ (U V : X.Opens) (f : U ⟶ V)
        (s : (I.cocomplex.X (n + 1)).obj.obj (op V)) hs hres,
        c U ((I.cocomplex.X (n + 1)).obj.map f.op s) hres =
          (G.cohomologyPresheaf (n + 1)).map f.op (c V s hs)) ∧
      (∀ (U : X.Opens) (t : (I.cocomplex.X n).obj.obj (op U)) hc,
        c U ((I.cocomplex.d n (n + 1)).hom.app (op U) t) hc = 0) := by
  let c : ∀ (U : X.Opens) (s : (I.cocomplex.X (n + 1)).obj.obj (op U)),
      (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) s = 0 →
        (G.cohomologyPresheaf (n + 1)).obj (op U) := fun U s hs ↦
    I.extMk ((sectionEquiv U _).symm s) (n + 2) rfl (by
      apply (sectionEquiv U _).injective
      rw [sectionEquiv_comp, Equiv.apply_symm_apply, hs, sectionEquiv_zero])
  refine ⟨c, ?_, ?_, ?_⟩
  · intro U ξ
    obtain ⟨a, ha, hξ⟩ := I.extMk_surjective ξ (n + 2) rfl
    have hs : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U)
        (sectionEquiv U _ a) = 0 := by
      rw [← sectionEquiv_comp, ha, sectionEquiv_zero]
    refine ⟨sectionEquiv U _ a, hs, ?_⟩
    simpa only [c, Equiv.symm_apply_apply] using hξ
  · intro U V f s hs hres
    have hmap : (sectionEquiv U _).symm
        ((I.cocomplex.X (n + 1)).obj.map f.op s) =
        (freeAbelianSheaf X).map f ≫ (sectionEquiv V _).symm s := by
      apply (sectionEquiv U _).injective
      rw [Equiv.apply_symm_apply, sectionEquiv_map, Equiv.apply_symm_apply]
    change I.extMk ((sectionEquiv U _).symm
      ((I.cocomplex.X (n + 1)).obj.map f.op s)) (n + 2) rfl _ =
        (Abelian.Ext.mk₀ ((freeAbelianSheaf X).map f)).comp
          (I.extMk ((sectionEquiv V _).symm s) (n + 2) rfl _) (zero_add _)
    rw [I.mk₀_comp_extMk]
    congr 1
  · intro U t hc
    apply (I.extMk_eq_zero_iff _ (n + 2) rfl _ n rfl).2
    refine ⟨(sectionEquiv U _).symm t, ?_⟩
    apply (sectionEquiv U _).injective
    rw [sectionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

-- Stacks 01FW: an exact triple of sheaves lifts kernel sections locally.
private theorem exact_sheaf_section_locally_boundary {X : Scheme.{u}}
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.Exact) (s : S.X₂.obj.obj (op ⊤))
    (hs : S.g.hom.app (op ⊤) s = 0) (x : X) :
    ∃ (U : X.Opens) (t : S.X₁.obj.obj (op U)), x ∈ U ∧
      S.f.hom.app (op U) t =
        S.X₂.obj.map (homOfLE (X := X.Opens) le_top).op s := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op (⊤ : X.Opens))
  have hK := (ShortComplex.kernelSequence_exact S.g).map_of_mono_of_preservesKernel
    E inferInstance inferInstance
  obtain ⟨k, hk⟩ : ∃ k : (Limits.kernel S.g).obj.obj (op ⊤),
      (Limits.kernel.ι S.g).hom.app (op ⊤) k = s :=
    (ShortComplex.ab_exact_iff _).1 hK s hs
  let f' := Limits.kernel.lift S.g S.f S.zero
  have : Epi f' := S.exact_iff_epi_kernel_lift.mp hS
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f'.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f').2 inferInstance
  obtain ⟨U, f, ⟨t, ht⟩, hx⟩ :=
    (Opens.mem_grothendieckTopology X).1 (Presheaf.imageSieve_mem _ f'.hom k) x
      (Opens.mem_top x)
  refine ⟨U, t, hx, ?_⟩
  have hfac := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun φ ↦ φ.hom) (Limits.kernel.lift_ι S.g S.f S.zero))
      (op U)) t
  have hnat := (Limits.kernel.ι S.g).hom.naturality_apply f.op k
  change (Limits.kernel.ι S.g).hom.app (op ⊤) k = s at hk
  calc
    S.f.hom.app (op U) t =
        (Limits.kernel.ι S.g).hom.app (op U) (f'.hom.app (op U) t) := hfac.symm
    _ = (Limits.kernel.ι S.g).hom.app (op U)
        ((Limits.kernel S.g).obj.map f.op k) := congrArg _ ht
    _ = S.X₂.obj.map f.op s := by rw [hnat, hk]

-- Cohomology uses the Ext localization instance for Zariski sheaves.
/-- Positive-degree cohomology classes on a scheme are locally zero.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0 (label `lemma-gabber-criterion`),
line 14228, proof; Cohomology on Sites, Lemma 01FW.  The cohomology groups and their
restriction maps are rendered by Mathlib's cohomology presheaf; an injective resolution
is included as the resolution used to compute the groups.
The assertion is the four-step proof in the node
(blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).
-/
theorem zariski_cohomology_class_locally_zero {X : Scheme.{u}}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (I : InjectiveResolution G) (q : ℕ) (hq : 0 < q)
    (ξ : (G.cohomologyPresheaf q).obj (op ⊤)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ((G.cohomologyPresheaf q).map
        (homOfLE (X := X.Opens) (x := U) (y := ⊤) le_top).op).hom ξ = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  obtain ⟨c, hrep, hres, hbd⟩ := zariski_resolution_cocycle_classes G I n
  obtain ⟨s, hs, hξ⟩ := hrep ⊤ ξ
  let S := ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))
  obtain ⟨U, t, hx, ht⟩ := exact_sheaf_section_locally_boundary S (I.exact_succ n) s hs x
  dsimp only [S] at ht
  have hcycle : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U)
      ((I.cocomplex.X (n + 1)).obj.map
        (homOfLE (X := X.Opens) (x := U) (y := ⊤) le_top).op s) = 0 := by
    rw [(I.cocomplex.d (n + 1) (n + 2)).hom.naturality_apply, hs]
    exact map_zero _
  refine ⟨U, hx, ?_⟩
  rw [← hξ, ← hres U ⊤ (homOfLE le_top) s hs hcycle]
  have hb := hbd U t (by simpa only [ht] using hcycle)
  simpa only [ht] using hb

end AlgebraicGeometry
