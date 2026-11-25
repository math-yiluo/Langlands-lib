/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars

/-! # Kernels of integral constructible internal module objects

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1).
(auxiliary; not a blueprint node)

The proof reduces to one local pivot and proves all repeated elimination and
finite-presentation glue. It uses the existing field local-triviality theorem to control
rational cokernels; full integral Smith invariants are not required.
-/

open CategoryTheory Limits

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

universe v u

@[expose] public section

section
variable {C : Type u} [Category.{v} C] [Abelian C]

@[irreducible] private noncomputable def pivotKernelIso {A B D E : C}
    (p : A ⟶ D) [Mono p] (r : B ⟶ A) (c : A ⟶ E) (d : B ⟶ E) :
    kernel (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)) ≅
      kernel (d - r ≫ c) := by
  let f := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
  let s := d - r ≫ c
  have htop : kernel.ι f ≫ biprod.fst = -(kernel.ι f ≫ biprod.snd ≫ r) := by
    apply (cancel_mono p).mp
    have h := kernel.condition f =≫ biprod.fst
    simpa only [f, biprod.lift_fst, Category.assoc, biprod.desc_eq,
      Preadditive.comp_add, Preadditive.comp_neg, Preadditive.neg_comp, zero_comp,
      eq_neg_iff_add_eq_zero] using h
  have hbot : (kernel.ι f ≫ biprod.snd) ≫ s = 0 := by
    have h := kernel.condition f =≫ biprod.snd
    rw [Category.assoc] at h
    rw [show f ≫ biprod.snd = biprod.desc c d from biprod.lift_snd _ _] at h
    simp only [zero_comp, biprod.desc_eq, Preadditive.comp_add,
      ← Category.assoc] at h
    rw [htop] at h
    simpa only [s, Preadditive.comp_sub, Preadditive.neg_comp, Category.assoc,
      neg_add_eq_sub] using h
  let a := kernel.lift s (kernel.ι f ≫ biprod.snd) hbot
  let b := kernel.lift f (biprod.lift (-(kernel.ι s ≫ r)) (kernel.ι s)) (by
    apply biprod.hom_ext
    · simp [f, Preadditive.neg_comp]
    · have h := kernel.condition s
      simpa only [f, Category.assoc, biprod.lift_snd, biprod.desc_eq,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.comp_add, zero_comp,
        Preadditive.neg_comp, s, Preadditive.comp_sub, neg_add_eq_sub] using h)
  refine ⟨a, b, ?_, ?_⟩
  · apply (cancel_mono (kernel.ι f)).mp
    apply biprod.hom_ext
    · simp [a, b, htop]
    · simp [a, b]
  · apply (cancel_mono (kernel.ι s)).mp
    simp [a, b]

@[irreducible] private noncomputable def kernelCokernelCompIso
    {B D E N : C} (b : D ⟶ E) (p : E ⟶ N) (w : b ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) (t : B ⟶ E) :
    let δ := biprod.desc b t
    let j := kernel.lift δ (kernel.ι b ≫ biprod.inl) (by simp [δ])
    cokernel j ≅ kernel (t ≫ p) := by
  let δ := biprod.desc b t
  let j := kernel.lift δ (kernel.ι b ≫ biprod.inl) (by simp [δ])
  let q := kernel.lift (t ≫ p)
    (kernel.ι δ ≫ biprod.snd) (by
      have h := kernel.condition δ =≫ p
      simpa only [δ, biprod.desc_eq, Preadditive.comp_add, Preadditive.add_comp,
        Category.assoc, w, comp_zero, zero_add, zero_comp] using h)
  have hjq : j ≫ q = 0 := by
    apply (cancel_mono (kernel.ι (t ≫ p))).1
    simp [j, q]
  have hex : (ShortComplex.mk j q hjq).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    have hxf : x ≫ kernel.ι δ ≫ biprod.snd = 0 := by
      have h := hx =≫ kernel.ι (t ≫ p)
      simpa only [Category.assoc, kernel.lift_ι, zero_comp, q] using h
    have hxs : (x ≫ kernel.ι δ ≫ biprod.fst) ≫ b = 0 := by
      have h := x ≫= kernel.condition δ
      simpa only [δ, biprod.desc_eq, Preadditive.comp_add, Category.assoc,
        ← Category.assoc, hxf, zero_comp, add_zero, comp_zero] using h
    refine ⟨T, 𝟙 T, inferInstance, kernel.lift b
      (x ≫ kernel.ι δ ≫ biprod.fst) hxs, ?_⟩
    apply (cancel_mono (kernel.ι δ)).1
    apply biprod.hom_ext
    · simp [j]
    · simp [j, hxf]
  have : Epi q := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T x
    have hw : (x ≫ kernel.ι (t ≫ p) ≫ t) ≫ p = 0 := by
      simp [Category.assoc]
    obtain ⟨T', σ, hσ, y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        hp _).mp hw
    let z := biprod.lift (-y) (σ ≫ x ≫ kernel.ι (t ≫ p))
    have hz : z ≫ δ = 0 := by simp [z, δ, hy]
    refine ⟨T', σ, hσ, kernel.lift δ z hz, ?_⟩
    apply (cancel_mono (kernel.ι (t ≫ p))).1
    simp [q, z]
  exact colimit.isoColimitCocone ⟨_, hex.gIsCokernel⟩

@[irreducible] private noncomputable def kernelDescCokernelIso
    {A B M N : C} (a : A ⟶ B) (p : B ⟶ M) (w : a ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) (f : M ⟶ N) :
    let l := kernel.lift (p ≫ f) a (by simp [reassoc_of% w])
    cokernel l ≅ kernel f := by
  have : Epi p := Cofork.IsColimit.epi hp
  let l := kernel.lift (p ≫ f) a (by simp [reassoc_of% w])
  let q := kernel.lift f (kernel.ι (p ≫ f) ≫ p) (by simp [Category.assoc])
  have hlq : l ≫ q = 0 := by
    apply (cancel_mono (kernel.ι f)).1
    simp [l, q, w]
  have hex : (ShortComplex.mk l q hlq).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    have hxp : (x ≫ kernel.ι (p ≫ f)) ≫ p = 0 := by
      have h := hx =≫ kernel.ι f
      simpa only [Category.assoc, kernel.lift_ι, zero_comp, q] using h
    obtain ⟨T', σ, hσ, y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hp _).mp hxp
    refine ⟨T', σ, hσ, y, ?_⟩
    apply (cancel_mono (kernel.ι (p ≫ f))).1
    simpa [l, Category.assoc] using hy
  have : Epi q := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T x
    obtain ⟨T', σ, hσ, y, hy⟩ :=
      surjective_up_to_refinements_of_epi p (x ≫ kernel.ι f)
    have hyf : y ≫ (p ≫ f) = 0 := by rw [← Category.assoc, ← hy]; simp
    refine ⟨T', σ, hσ, kernel.lift (p ≫ f) y hyf, ?_⟩
    apply (cancel_mono (kernel.ι f)).1
    simpa [q] using hy
  exact colimit.isoColimitCocone ⟨_, hex.gIsCokernel⟩

@[irreducible] private noncomputable def pivotCokernelIso {A B D E : C}
    (p : A ⟶ D) [IsIso p] (r : B ⟶ A) (c : A ⟶ E) (d : B ⟶ E) :
    cokernel (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)) ≅
      cokernel (d - r ≫ c) := by
  let f := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
  let s := d - r ≫ c
  let q := biprod.desc (-(inv p ≫ c ≫ cokernel.π s)) (cokernel.π s)
  have hfq : f ≫ q = 0 := by
    apply biprod.hom_ext'
    · simp [f, q, biprod.lift_eq, Preadditive.add_comp, Preadditive.comp_add]
    · simpa [f, q, biprod.lift_eq, Preadditive.add_comp, Preadditive.comp_add,
        Preadditive.sub_comp, s, sub_eq_add_neg, add_comm] using cokernel.condition s
  let j := biprod.inr ≫ cokernel.π f
  have hsj : s ≫ j = 0 := by
    have h := biprod.lift (-r) (𝟙 B) ≫= cokernel.condition f
    simpa [f, j, s, biprod.lift_eq, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.sub_comp, sub_eq_add_neg, add_comm] using h
  let a := cokernel.desc f q hfq
  let b := cokernel.desc s j hsj
  have hfirst : biprod.inl ≫ cokernel.π f = -(inv p ≫ c ≫ j) := by
    apply (cancel_epi p).mp
    have h := biprod.inl ≫= cokernel.condition f
    simpa [f, j, biprod.lift_eq, Preadditive.add_comp, Preadditive.comp_add,
      eq_neg_iff_add_eq_zero] using h
  refine ⟨a, b, ?_, ?_⟩
  · change a ≫ b = 𝟙 (cokernel f)
    apply (cancel_epi (cokernel.π f)).mp
    apply biprod.hom_ext'
    · simp only [Category.comp_id, Category.assoc, a, b, cokernel.π_desc_assoc,
        cokernel.π_desc, biprod.inl_desc_assoc, q, Preadditive.neg_comp]
      exact hfirst.symm
    · simp [a, b, q, j]
  · change b ≫ a = 𝟙 (cokernel s)
    apply (cancel_epi (cokernel.π s)).mp
    simp [a, b, j, q]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

@[irreducible] private noncomputable def mappedPivotCokernelIso
    {D' : Type*} [Category D'] [Abelian D'] (F : C ⥤ D')
    [F.Additive] [PreservesFiniteColimits F]
    {A B D E : C} (p : A ⟶ D) [IsIso (F.map p)]
    (r : B ⟶ A) (c : A ⟶ E) (d : B ⟶ E) :
    F.obj (cokernel (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d))) ≅
      F.obj (cokernel (d - r ≫ c)) := by
  let f := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
  let b := biprod.lift (biprod.desc (F.map p) (F.map r ≫ F.map p))
    (biprod.desc (F.map c) (F.map d))
  have h : (F.mapBiprod A B).hom ≫ b = F.map f ≫ (F.mapBiprod D E).hom := by
    dsimp only [b, f]
    rw [biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst]
      rw [← F.map_comp]
      exact biprod.mapBiprod_hom_desc F A B p (r ≫ p)
    · simp only [Category.assoc, biprod.lift_snd]
      exact biprod.mapBiprod_hom_desc F A B c d
  exact PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) b (F.mapBiprod A B) (F.mapBiprod D E) h.symm ≪≫
    pivotCokernelIso (F.map p) (F.map r) (F.map c) (F.map d) ≪≫
    cokernelIsoOfEq (by simp only [Functor.map_sub, F.map_comp]) ≪≫
    (PreservesCokernel.iso F (d - r ≫ c)).symm

omit [Abelian C] in
private lemma conjugate_eq {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : eA.inv ≫ f ≫ eB.hom = g) :
    eA.hom ≫ g = f ≫ eB.hom := by
  rw [← h]
  simp only [Iso.hom_inv_id_assoc]

omit [Abelian C] in
private lemma map_comp_squares {D' : Type*} [Category D'] (G : C ⥤ D')
    {R S R' S' : C} {R'' S'' : D'} (φ : R ⟶ S) (φ' : R' ⟶ S')
    (ψ : R'' ⟶ S'') (e : R ⟶ R') (d : S ⟶ S')
    (e' : G.obj R' ⟶ R'') (d' : G.obj S' ⟶ S'')
    (h : e ≫ φ' = φ ≫ d) (h' : e' ≫ ψ = G.map φ' ≫ d') :
    (G.map e ≫ e') ≫ ψ = G.map φ ≫ (G.map d ≫ d') := by
  rw [Category.assoc, h', ← Category.assoc, ← G.map_comp, h, G.map_comp,
    Category.assoc]

private lemma map_pullback_section {D' : Type*} [Category D'] (F : C ⥤ D')
    {A B T : C} (p : A ⟶ T) (q : B ⟶ T)
    [IsSplitEpi (F.map (pullback.snd p q))] :
    (section_ (F.map (pullback.snd p q)) ≫ F.map (pullback.fst p q)) ≫ F.map p =
      F.map q := by
  rw [Category.assoc, ← F.map_comp, pullback.condition, F.map_comp,
    ← Category.assoc, IsSplitEpi.id, Category.id_comp]

end

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint laxBraided_upperStarFromPoint
attribute [local irreducible] cokernelPresentationIso

-- Keep the cached monoid structures folded during repeated instance comparisons.
set_option warn.classDefReducibility false in
private noncomputable def pulledMonObj {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    MonObj ((ProEtale.upperStar Ab.{u + 1} g).obj R) := inferInstance

set_option warn.classDefReducibility false in
private noncomputable def coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) := inferInstance

set_option warn.classDefReducibility false in
attribute [local instance 2000] pulledMonObj coefficientMonObj
attribute [local irreducible] Mod.extendScalars Mod.comap
  AlgebraicGeometry.ProEtale.upperStar Functor.mapMod

private abbrev DescendedMatrixKernels (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
    IsLocallyFinitelyPresented R P →
    ∀ (Y Z : Scheme.{u}) (g : Y ⟶ X) (h : Z ⟶ Y),
      let F := (ProEtale.upperStar Ab.{u + 1} g).mapMod R
      let G := (ProEtale.upperStar Ab.{u + 1} h).mapMod ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      ∀ (A B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} h).obj ((ProEtale.upperStar Ab.{u + 1} g).obj R)))
        (a : A ⟶ B),
        Mod.IsFree _ A → Mod.IsFree _ B →
        (cokernel a ≅ G.obj (F.obj P)) →
        IsLocallyFinitelyPresented
          ((ProEtale.upperStar Ab.{u + 1} h).obj ((ProEtale.upperStar Ab.{u + 1} g).obj R))
          (kernel a)

private lemma lfp_of_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsLocallyFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    IsLocallyFinitelyPresented R M := by
  choose V hV using h
  refine ⟨U.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (fp_pullback_comp_iff ((V i).f j) (U.f i) M).mpr (hV i j)

-- Two successive module pullbacks require additional elaboration heartbeats.
private lemma lfp_kernel_of_descended_matrix_kernels {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (hker : DescendedMatrixKernels X R)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : IsLocallyFinitelyPresented R M) (hN : IsLocallyFinitelyPresented R N) :
    IsLocallyFinitelyPresented R (kernel f) := by
  have hC : IsLocallyFinitelyPresented R (cokernel f) := lfp_cokernel f hM hN
  obtain ⟨U, hU⟩ := common_fp_cover hM hN
  apply lfp_of_cover U
  intro i
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
  let R' := (ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R
  let : F.Additive := inferInstance
  let : PreservesFiniteLimits F := inferInstance
  let : PreservesFiniteColimits F := inferInstance
  obtain ⟨n, m, a, ⟨eM⟩⟩ := (hU i).1
  obtain ⟨p, q, b, ⟨eN⟩⟩ := (hU i).2
  let πM := cokernel.π a ≫ eM.inv
  let πN := cokernel.π b ≫ eN.inv
  have : Epi πN := by dsimp [πN]; infer_instance
  let v := pullback.snd πN (πM ≫ F.map f)
  have : Epi v := by dsimp [v]; infer_instance
  obtain ⟨V, hV⟩ := AlgebraicGeometry.ProEtale.freeEpiLocalSplitting
    (U.X i) R' _ _ v ⟨n, ⟨Iso.refl _⟩⟩
  apply lfp_of_cover V
  intro j
  let G := (ProEtale.upperStar Ab.{u + 1} (V.f j)).mapMod R'
  let R'' := (ProEtale.upperStar Ab.{u + 1} (V.f j)).obj R'
  let : G.Additive := inferInstance
  let : PreservesFiniteLimits G := inferInstance
  let : PreservesFiniteColimits G := inferInstance
  have : IsSplitEpi (G.map v) := hV j
  let t := section_ (G.map v) ≫ G.map (pullback.fst πN (πM ≫ F.map f))
  have ht : t ≫ G.map πN = G.map πM ≫ G.map (F.map f) := by
    exact (map_pullback_section G πN (πM ≫ F.map f)).trans
      (G.map_comp πM (F.map f))
  obtain ⟨iM, hπM⟩ : ∃ iM : G.obj (F.obj M) ≅ cokernel (G.map a),
      G.map πM ≫ iM.hom = cokernel.π (G.map a) := by
    refine ⟨G.mapIso eM ≪≫ PreservesCokernel.iso G a, ?_⟩
    simp [πM]
  obtain ⟨iN, hπN⟩ : ∃ iN : G.obj (F.obj N) ≅ cokernel (G.map b),
      G.map πN ≫ iN.hom = cokernel.π (G.map b) := by
    refine ⟨G.mapIso eN ≪≫ PreservesCokernel.iso G b, ?_⟩
    simp [πN]
  let φ := iM.inv ≫ G.map (F.map f) ≫ iN.hom
  have hφ : t ≫ cokernel.π (G.map b) = cokernel.π (G.map a) ≫ φ := by
    rw [← hπN, ← Category.assoc, ht]
    simp [φ, ← hπM]
  let δ := biprod.desc (G.map b) t
  have hfree (r : ℕ) : Mod.IsFree R'' (G.obj (Mod.finiteFree R' r)) :=
    free_pullback (V.f j) ⟨r, ⟨Iso.refl _⟩⟩
  let eδ : G.obj (F.obj (cokernel f)) ≅ cokernel δ :=
    G.mapIso (PreservesCokernel.iso F f) ≪≫
      PreservesCokernel.iso G (F.map f) ≪≫
      cokernel.mapIso (G.map (F.map f)) φ iM iN (by simp [φ]) ≪≫
      cokernelPresentationIso (G.map a) (G.map b) φ t hφ
  have hKb := hker N hN (U.X i) (V.X j) (U.f i) (V.f j)
    _ _ (G.map b) (hfree q) (hfree p) iN.symm
  have hKδ := hker (cokernel f) hC (U.X i) (V.X j) (U.f i) (V.f j)
    _ _ δ (free_biprod (hfree q) (hfree n)) (hfree p) eδ.symm
  have wN : G.map b ≫ G.map πN = 0 := by
    simp only [← G.map_comp, πN, cokernel.condition_assoc, zero_comp, G.map_zero]
  have hpN : IsColimit (CokernelCofork.ofπ (G.map πN) wN) :=
    IsColimit.ofIsoColimit (cokernelIsCokernel (G.map b))
      (Cofork.ext iN.symm (by
        change cokernel.π (G.map b) ≫ iN.inv = G.map πN
        rw [← hπN]
        simp))
  let κ := kernel.lift δ (kernel.ι (G.map b) ≫ biprod.inl) (by simp [δ])
  have hE : IsLocallyFinitelyPresented R'' (kernel (G.map πM ≫ G.map (F.map f))) := by
    exact lfp_of_iso
      (lfp_of_iso (lfp_cokernel κ hKb hKδ)
        (kernelCokernelCompIso (G.map b) (G.map πN) wN hpN t))
      (kernelIsoOfEq ht)
  have wM : G.map a ≫ G.map πM = 0 := by
    simp only [← G.map_comp, πM, cokernel.condition_assoc, zero_comp, G.map_zero]
  have hpM : IsColimit (CokernelCofork.ofπ (G.map πM) wM) :=
    IsColimit.ofIsoColimit (cokernelIsCokernel (G.map a))
      (Cofork.ext iM.symm (by
        change cokernel.π (G.map a) ≫ iM.inv = G.map πM
        rw [← hπM]
        simp))
  let l :=  kernel.lift (G.map πM ≫ G.map (F.map f)) (G.map a)
    (by simp [reassoc_of% wM])
  have hA : IsLocallyFinitelyPresented R'' (G.obj (Mod.finiteFree R' m)) := by
    exact ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun _ ↦
      fp_pullback _ (fp_of_free (hfree m))⟩
  have hK := lfp_of_iso (lfp_cokernel l hA hE)
    (kernelDescCokernelIso (G.map a) (G.map πM) wM hpM (G.map (F.map f)))
  exact lfp_of_iso hK (PreservesKernel.iso (F ⋙ G) f).symm

private lemma locally_free_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
        ((ProEtale.upperStar Ab.{u + 1} g).obj R))
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj
          (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.pullback₁ g, fun i ↦ ?_⟩
  change Mod.IsFree _
    (((ProEtale.upperStar Ab.{u + 1} (pullback.fst g (U.f i))).mapMod _).obj _)
  apply (free_pullback_comp_iff (pullback.fst g (U.f i)) g M).mp
  rw [pullback.condition]
  exact (free_pullback_comp_iff (pullback.snd g (U.f i)) (U.f i) M).mpr
    (free_pullback (pullback.snd g (U.f i)) (hU i))

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

@[irreducible] private noncomputable def extendScalarsComapSquareIso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj R'] [IsCommMonObj S']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (e : R ⟶ R') [IsMonHom e] [IsIso e]
    (d : S ⟶ S') [IsMonHom d] [IsIso d] (hsq : e ≫ ψ = φ ≫ d) :
    Mod.comap (inv e) ⋙ Mod.extendScalars ψ ≅
      Mod.extendScalars φ ⋙ Mod.comap (inv d) := by
  let a := (Mod.comapEquivalenceOfIsIso e).symm.toAdjunction.comp
    (Mod.extendRestrictAdjunction ψ)
  let b := (Mod.extendRestrictAdjunction φ).comp
    (Mod.comapEquivalenceOfIsIso d).symm.toAdjunction
  have h : Mod.comap d ⋙ Mod.comap φ ≅ Mod.comap ψ ⋙ Mod.comap e :=
    (Mod.comapComp φ d).symm ≪≫ Mod.comapCongr hsq.symm ≪≫ Mod.comapComp e ψ
  exact a.leftAdjointUniq (b.ofNatIsoRight h)

private abbrev RationalCokernelFree {X : Scheme.{u}}
    {A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)} (a : A ⟶ B) : Prop :=
  ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
        ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
          (cokernel a)))

omit [FiniteDimensional ℚ_[ℓ] E] in
private lemma rationalCokernelFree_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)} (a : A ⟶ B)
    (ha : RationalCokernelFree ℓ E a) :
    let T := (ProEtale.upperStar Ab.{u + 1} g).mapMod
        (condensedRingObj (integralCoeff ℓ E) X) ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) g))
    RationalCokernelFree ℓ E (T.map a) := by
  let F := ProEtale.upperStar Ab.{u + 1} g
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let ψ := coefficientMap (integralScalarMap ℓ E) Y
  let e := condensedPullbackHom (integralCoeff ℓ E) g
  let d := condensedPullbackHom (Profinite.continuousMapRingObj E) g
  let K := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv d)
  let T := F.mapMod R ⋙ Mod.comap (inv e)
  have hsq : e ≫ ψ = F.map φ ≫ d :=
    (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) g).symm
  let i : (Mod.extendScalars ψ).obj (cokernel (T.map a)) ≅
      K.obj ((F.mapMod S).obj ((Mod.extendScalars φ).obj (cokernel a))) :=
    (Mod.extendScalars ψ).mapIso (PreservesCokernel.iso T a).symm ≪≫
      (extendScalarsComapSquareIso (F.map φ) ψ e d hsq).app
        ((F.mapMod R).obj (cokernel a)) ≪≫
      K.mapIso ((pullbackExtendScalarsComparison g R S φ).symm.app (cokernel a))
  exact locally_free_of_iso
    (locally_free_comap (inv d) (locally_free_pullback g ha)) i.symm

private abbrev IntegralMatrixPivots : Prop :=
  ∀ (n : ℕ) (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
    Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
    (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) →
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      T.map a = 0 ∨
        ∃ (m : ℕ), m < n ∧
          ∃ (A₁ B₁ : Mod (Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) R)
            (_ : A₁ ≅ Mod.finiteFree R m),
            Mod.IsFree R B₁ ∧
              ∃ (p : Mod.regular R ⟶ Mod.regular R), Mono p ∧
                IsIso ((Mod.extendScalars
                  (coefficientMap (integralScalarMap ℓ E) (V.X k))).map p) ∧
                ∃ (r : A₁ ⟶ Mod.regular R) (c : Mod.regular R ⟶ B₁) (d : A₁ ⟶ B₁)
                  (eA : T.obj A ≅ Mod.regular R ⊞ A₁)
                  (eB : T.obj B ≅ Mod.regular R ⊞ B₁),
                  eA.inv ≫ T.map a ≫ eB.hom =
                    biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)

private lemma lfp_of_fp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : IsLocallyFinitelyPresented R M := by
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    .singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _)
  exact ⟨U, fun _ ↦ fp_pullback _ h⟩

private abbrev IntegralMatrixKernels : Prop :=
  ∀ (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) A →
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
    (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) →
    IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) (kernel a)

-- Strong induction removes one integral pivot and preserves the smaller rational cokernel.
omit [FiniteDimensional ℚ_[ℓ] E] in
private lemma integralMatrixKernels_of_pivots
    (hchart : IntegralMatrixPivots.{u} ℓ E) : IntegralMatrixKernels.{u} ℓ E := by
  have H (n : ℕ) : ∀ (X : Scheme.{u})
      (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
      Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
      Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
      (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
            (condensedRingObj (Profinite.continuousMapRingObj E) X))
          (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
            ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
              (cokernel a)))) →
      IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) (kernel a) := by
    induction n using Nat.strong_induction_on with
    | h n IH =>
      intro X A B a hA hB hLF
      obtain ⟨V, hV⟩ := hchart n X A B a hA hB hLF
      apply lfp_of_cover V
      intro k
      let R := condensedRingObj (integralCoeff ℓ E) X
      let R' := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let F := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod R
      let α := condensedPullbackHom (integralCoeff ℓ E) (V.f k)
      let J := Mod.comap (D := Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) (inv α)
      let T := F ⋙ J
      have hT : IsLocallyFinitelyPresented R' (kernel (T.map a)) := by
        rcases hV k with hz | ⟨m, hmn, A₁, B₁, iA, hB₁, p, hp, hunit, r, c, d, eA, eB, he⟩
        · exact lfp_of_iso (lfp_of_fp (fp_of_free
            (free_comap (inv α) (free_pullback (V.f k) ⟨n, hA⟩))))
            (kernelZeroIsoSource.symm ≪≫ (kernelIsoOfEq hz).symm)
        · let _ := hp
          let b := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
          let e : kernel (T.map a) ≅ kernel b :=
            kernel.mapIso (T.map a) b eA eB (conjugate_eq eA eB (T.map a) b he).symm
          let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (V.X k))
          have : IsIso (L.map p) := hunit
          let eC : cokernel (T.map a) ≅ cokernel b :=
            cokernel.mapIso (T.map a) b eA eB (conjugate_eq eA eB (T.map a) b he).symm
          let eS := L.mapIso eC ≪≫ mappedPivotCokernelIso L p r c d
          have hS : RationalCokernelFree ℓ E (d - r ≫ c) :=
            locally_free_of_iso (rationalCokernelFree_pullback ℓ E (V.f k) a hLF) eS
          have hK := IH m hmn (V.X k) A₁ B₁ (d - r ≫ c) ⟨iA⟩ hB₁ hS
          exact lfp_of_iso hK ((pivotKernelIso p r c d).symm ≪≫ e.symm)
      have hJ := lfp_of_iso hT (PreservesKernel.iso J (F.map a)).symm
      have hF := lfp_of_comap (inv α) hJ
      exact lfp_of_iso hF (PreservesKernel.iso F a).symm
  intro X A B a hA hB hLF
  obtain ⟨n, hn⟩ := hA
  exact H n X A B a hn hB hLF

private abbrev RationalMatrixKernels : Prop :=
  ∀ (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Y Z : Scheme.{u}) (g : Y ⟶ X) (h : Z ⟶ Y),
    let R := condensedRingObj (integralCoeff ℓ E) X
    let S := condensedRingObj (Profinite.continuousMapRingObj E) X
    let R' := (ProEtale.upperStar Ab.{u + 1} g).obj R
    let R'' := (ProEtale.upperStar Ab.{u + 1} h).obj R'
    let S'' := (ProEtale.upperStar Ab.{u + 1} h).obj
      ((ProEtale.upperStar Ab.{u + 1} g).obj S)
    let φ := (ProEtale.upperStar Ab.{u + 1} h).map
      ((ProEtale.upperStar Ab.{u + 1} g).map (coefficientMap (integralScalarMap ℓ E) X))
    ∀ (A B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R'') (a : A ⟶ B),
      Mod.IsFree R'' A → Mod.IsFree R'' B →
      (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage Z, ∀ k,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj S'')
          (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod S'').obj
            ((Mod.extendScalars φ).obj (cokernel a)))) →
      IsLocallyFinitelyPresented R'' (kernel a)

-- Two successive module pullbacks require additional elaboration heartbeats.
omit [FiniteDimensional ℚ_[ℓ] E] in
private lemma rationalMatrixKernels_of_integral
    (hmat : IntegralMatrixKernels.{u} ℓ E) : RationalMatrixKernels.{u} ℓ E := by
  intro X _ Y Z g h
  dsimp only
  intro A B a hA hB hLF
  let F := ProEtale.upperStar Ab.{u + 1} g
  let G := ProEtale.upperStar Ab.{u + 1} h
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := G.map (F.map (coefficientMap (integralScalarMap ℓ E) X))
  let ψ := coefficientMap (integralScalarMap ℓ E) Z
  let e := G.map (condensedPullbackHom (integralCoeff ℓ E) g) ≫
    condensedPullbackHom (integralCoeff ℓ E) h
  let d := G.map (condensedPullbackHom (Profinite.continuousMapRingObj E) g) ≫
    condensedPullbackHom (Profinite.continuousMapRingObj E) h
  have : IsMonHom e := by dsimp [e]; infer_instance
  have : IsIso e := by dsimp [e]; infer_instance
  have : IsMonHom d := by dsimp [d]; infer_instance
  have : IsIso d := by dsimp [d]; infer_instance
  have hsq : e ≫ ψ = φ ≫ d := by
    exact map_comp_squares G (F.map (coefficientMap (integralScalarMap ℓ E) X))
      (coefficientMap (integralScalarMap ℓ E) Y) ψ
      (condensedPullbackHom (integralCoeff ℓ E) g)
      (condensedPullbackHom (Profinite.continuousMapRingObj E) g)
      (condensedPullbackHom (integralCoeff ℓ E) h)
      (condensedPullbackHom (Profinite.continuousMapRingObj E) h)
      (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) g).symm
      (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) h).symm
  let T := Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (inv e)
  let e' : (Mod.extendScalars ψ).obj (cokernel (T.map a)) ≅
      (Mod.comap (inv d)).obj ((Mod.extendScalars φ).obj (cokernel a)) :=
    (Mod.extendScalars ψ).mapIso (PreservesCokernel.iso T a).symm ≪≫
      (extendScalarsComapSquareIso φ ψ e d hsq).app (cokernel a)
  have hLF' := locally_free_of_iso (locally_free_comap (inv d) hLF) e'.symm
  have hK := hmat Z (T.obj A) (T.obj B) (T.map a)
    (free_comap (inv e) hA) (free_comap (inv e) hB) hLF'
  have hT := lfp_of_iso hK (PreservesKernel.iso T a).symm
  exact lfp_of_comap (inv e) hT

private lemma descendedMatrixKernels_of_rational
    (hmat : RationalMatrixKernels.{u} ℓ E)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    DescendedMatrixKernels X (condensedRingObj (integralCoeff ℓ E) X) := by
  intro P hP Y Z g h
  dsimp only
  intro A B a hA hB e
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let F := ProEtale.upperStar Ab.{u + 1} g
  let G := ProEtale.upperStar Ab.{u + 1} h
  let P_E := (Mod.extendScalars φ).obj P
  have hPE : IsLocallyFinitelyPresented S P_E := lfp_extend R S φ hP
  have hLF : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj S)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod S).obj P_E) := by
    let ψ := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
    have : IsMonHom ψ.hom := Sheaf.isMonHom_sheafCompose_map _ (liftCoefficientIso E).hom
    let ψX := (upperStarFromPoint X).map ψ.hom
    let E' := ULift.{u} E
    let : NormedField E' :=
      { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
        norm_mul a b := norm_mul a.down b.down }
    have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
      Sheaf.isCommMonObj_sheafCompose_obj
        (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
        (by
          intro T a b
          apply ULift.ext
          change (a.down * b.down : C(T.unop, E')) = b.down * a.down
          exact mul_comm a.down b.down)
    have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
      ((Mod.comap (inv ψX)).obj P_E) (lfp_comap (inv ψX) hPE)
    exact locally_free_of_iso (locally_free_comap ψX h)
      ((Mod.comapEquivalenceOfIsIso ψX).counitIso.app P_E)
  have hLF' := locally_free_pullback h (locally_free_pullback g hLF)
  let e' : (Mod.extendScalars (G.map (F.map φ))).obj (cokernel a) ≅
      ((G.mapMod (F.obj S)).obj ((F.mapMod S).obj P_E)) :=
    (Mod.extendScalars _).mapIso e ≪≫
      ((pullbackExtendScalarsComparison h (F.obj R) (F.obj S) (F.map φ)).app
        ((F.mapMod R).obj P)).symm ≪≫
      (G.mapMod (F.obj S)).mapIso ((pullbackExtendScalarsComparison g R S φ).app P).symm
  exact hmat X Y Z g h A B a hA hB
    (locally_free_of_iso hLF' e'.symm)

private lemma integral_lfp_kernel_of_rational
    (hmat : RationalMatrixKernels.{u} ℓ E)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)} (f : M ⟶ N)
    (hM : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) M)
    (hN : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) N) :
    IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) (kernel f) := by
  exact lfp_kernel_of_descended_matrix_kernels
    (descendedMatrixKernels_of_rational ℓ E hmat X) f hM hN

-- The restriction and coefficient equivalence are composed on module kernels.
private lemma integral_constructible_kernel_of_rational
    (hmat : RationalMatrixKernels.{u} ℓ E)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)} (f : M ⟶ N)
    (hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) N) :
    IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) (kernel f) := by
  obtain ⟨S, hS⟩ := common_lfp_stratification hM hN
  refine ⟨S, fun a ↦ ?_⟩
  have : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  let R := condensedRingObj (integralCoeff ℓ E) X
  let F := (ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R
  let φ := condensedPullbackHom (integralCoeff ℓ E) (S.immersion a)
  let T := Mod.comap (D := Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
    (inv φ)
  have hK := integral_lfp_kernel_of_rational ℓ E hmat (S.domain a) (T.map (F.map f))
    (lfp_comap (inv φ) (hS a).1) (lfp_comap (inv φ) (hS a).2)
  let e : (Mod.comap φ).obj (kernel (T.map (F.map f))) ≅ F.obj (kernel f) :=
    (Mod.comap φ).mapIso (PreservesKernel.iso T (F.map f)).symm ≪≫
      (Mod.comapEquivalenceOfIsIso φ).counitIso.app (kernel (F.map f)) ≪≫
      (PreservesKernel.iso F f).symm
  exact lfp_of_iso (lfp_comap φ hK) e

/-- Conditional assembly used while developing the integral matrix argument. -/
private theorem integralConstructible_kernels_of_rational
    (hmat : RationalMatrixKernels.{u} ℓ E)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) := by
  refine ⟨?_⟩
  rintro Y ⟨f, k, hk, hf⟩
  exact constructible_of_iso
    (integral_constructible_kernel_of_rational ℓ E hmat X f hf.1 hf.2)
    (limit.isoLimitCone ⟨k, hk⟩)

/-- Kernels of maps of integral constructible internal module objects are constructible.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1).
(auxiliary; not a blueprint node)

Proof:
1. For a map between finite free integral modules whose rational cokernel is locally
   free, use the one-pivot covering and strong induction on the number of source
   generators. A zero matrix has its free source as kernel. For a pivot block
   ((p,r p),(c,d)), monicity of p identifies the kernel with ker(d-r c). After
   scalar extension p is invertible, and the cokernel is the cokernel of d-r c.
   Thus the rational local-freeness hypothesis is inherited by the smaller matrix.
2. If a cokernel presentation descends from a locally finitely presented module on
   the noetherian base, extend that module to E. The existing field local-triviality
   theorem makes it locally free. Pull back this covering and use the coefficient
   and scalar-extension comparisons; step 1 therefore applies to the presentation.
3. For arbitrary locally finitely presented M and N, their cokernel is locally
   finitely presented. Choose common local presentations M=coker a and N=coker b.
   Locally lift the free generators of M through the free presentation of N, using
   the existing local splitting of an epimorphism onto a finite free module. If t
   is the lift, delta=(b,t) presents coker(M -> N). Step 2 gives locally finitely
   presented kernels of b and delta. Their natural map has cokernel
   ker(pi_M followed by f), by exactness in the abelian module category. Taking the
   cokernel of the map from the source relation module a then gives ker f. Generic
   cokernel closure proves local finite presentation at both stages. This argument
   includes torsion source and target modules.
4. Refine the constructible stratifications of M and N. Every stratum is noetherian.
   Apply step 3 there; inverse image preserves kernels, and the coefficient
   pullback isomorphisms transport the result to the original restricted modules.
   Finally transport the canonical kernel to any kernel cone. -/
theorem integralConstructible_kernels (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) := by
  have hchart : IntegralMatrixPivots.{u} ℓ E := integralMatrix_pivot_cover ℓ E
  have hmatrix : IntegralMatrixKernels.{u} ℓ E :=
    integralMatrixKernels_of_pivots ℓ E hchart
  have hrational : RationalMatrixKernels.{u} ℓ E :=
    rationalMatrixKernels_of_integral ℓ E hmatrix
  exact integralConstructible_kernels_of_rational ℓ E hrational X

end AlgebraicGeometry.ProEtale.CondensedRing
