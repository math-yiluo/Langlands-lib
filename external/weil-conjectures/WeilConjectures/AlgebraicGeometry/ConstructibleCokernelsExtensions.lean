/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre

/-! # Cokernels and extensions of constructible internal module sheaves

Source: finite presentation and local generator lifting.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def cokernelPresentationIso
    {A B D E : C} (a : A ⟶ B) (b : D ⟶ E)
    (f : cokernel a ⟶ cokernel b) (t : B ⟶ E)
    (ht : t ≫ cokernel.π b = cokernel.π a ≫ f) :
    cokernel f ≅ cokernel (biprod.desc b t) := by
  let δ := biprod.desc b t
  have hb : b ≫ cokernel.π δ = 0 := by
    have h := congrArg (fun k => biprod.inl ≫ k) (cokernel.condition δ)
    simpa only [← Category.assoc, δ, biprod.inl_desc, comp_zero] using h
  have ht' : t ≫ cokernel.π δ = 0 := by
    have h := congrArg (fun k => biprod.inr ≫ k) (cokernel.condition δ)
    simpa only [← Category.assoc, δ, biprod.inr_desc, comp_zero] using h
  let ψ : cokernel b ⟶ cokernel δ := cokernel.desc b (cokernel.π δ) hb
  have hf : f ≫ ψ = 0 := by
    apply (cancel_epi (cokernel.π a)).1
    simp only [comp_zero, ← Category.assoc, ← ht]
    simp [ψ, ht']
  have hδ : δ ≫ (cokernel.π b ≫ cokernel.π f) = 0 := by
    apply biprod.hom_ext'
    · simp [δ]
    · simp [δ, reassoc_of% ht]
  refine ⟨cokernel.desc f ψ hf,
    cokernel.desc δ (cokernel.π b ≫ cokernel.π f) hδ, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π f)).1
    apply (cancel_epi (cokernel.π b)).1
    simp [ψ]
  · apply (cancel_epi (cokernel.π δ)).1
    simp [ψ, δ]

end

open MonoidalCategory MonObj in
section
variable {C : Type*} [Category* C] [Abelian C]

private noncomputable def cokernel_inl_iso {A B D : C} (a : A ⟶ B) :
    cokernel (a ≫ (biprod.inl : B ⟶ B ⊞ D)) ≅ cokernel a ⊞ D := by
  let δ := a ≫ (biprod.inl : B ⟶ B ⊞ D)
  have h : a ≫ biprod.inl ≫ cokernel.π δ = 0 := by
    simpa only [δ, Category.assoc] using cokernel.condition δ
  refine ⟨cokernel.desc δ (biprod.map (cokernel.π a) (𝟙 D)) (by simp [δ]),
    biprod.desc (cokernel.desc a (biprod.inl ≫ cokernel.π δ) h)
      (biprod.inr ≫ cokernel.π δ), ?_, ?_⟩
  · apply (cancel_epi (cokernel.π δ)).1
    apply biprod.hom_ext' <;> simp [δ]
  · apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π a)).1
      simp [δ]
    · simp [δ]

private noncomputable def cokernel_pullback_iso
    {A B N M : C} (a : A ⟶ B) (p : B ⟶ N) (w : a ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) (g : M ⟶ N) :
    cokernel (pullback.lift (f := g) (g := p) (0 : A ⟶ M) a (by simpa using w.symm)) ≅ M := by
  have : Epi p := Cofork.IsColimit.epi hp
  let k := pullback.lift (f := g) (g := p) (0 : A ⟶ M) a (by simpa using w.symm)
  let π := pullback.fst g p
  have hk : k ≫ π = 0 := by simp [k, π]
  have hE : (ShortComplex.mk k π hk).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    have hxp : (x ≫ pullback.snd g p) ≫ p = 0 := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      change (x ≫ π) ≫ g = 0
      rw [hx, zero_comp]
    obtain ⟨T', σ, hσ, y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hp
        (x ≫ pullback.snd g p)).mp hxp
    refine ⟨T', σ, hσ, y, ?_⟩
    apply pullback.hom_ext
    · simpa [k, π, Category.assoc] using congrArg (σ ≫ ·) hx
    · simpa [k, Category.assoc] using hy
  have : Epi π := by dsimp [π]; infer_instance
  exact colimit.isoColimitCocone ⟨_, hE.gIsCokernel⟩

private lemma shortExact_pullback (Q : ShortComplex C) (hQ : Q.ShortExact)
    {P : C} (p : P ⟶ Q.X₃) :
    (ShortComplex.mk
      (pullback.lift (f := Q.g) (g := p) Q.f (0 : Q.X₁ ⟶ P) (by simp))
      (pullback.snd Q.g p) (by simp)).ShortExact := by
  have : Mono Q.f := hQ.mono_f
  have : Epi Q.g := hQ.epi_g
  let l := pullback.lift (f := Q.g) (g := p) Q.f (0 : Q.X₁ ⟶ P) (by simp)
  have : Mono l := mono_of_mono_fac (show l ≫ pullback.fst Q.g p = Q.f by simp [l])
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  have hxg : (x ≫ pullback.fst Q.g p) ≫ Q.g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, zero_comp]
  obtain ⟨T', σ, hσ, y, hy⟩ := hQ.exact.exact_up_to_refinements _ hxg
  refine ⟨T', σ, hσ, y, ?_⟩
  apply pullback.hom_ext
  · simpa [l, Category.assoc] using hy
  · simp [Category.assoc, hx]

end

private lemma lfp_cokernel_of_fp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : Mod.IsFinitelyPresented R M) (hN : Mod.IsFinitelyPresented R N) :
    IsLocallyFinitelyPresented R (cokernel f) := by
  obtain ⟨n, m, a, ⟨i⟩⟩ := hM
  obtain ⟨p, q, b, ⟨j⟩⟩ := hN
  let πM := cokernel.π a ≫ i.inv
  let πN := cokernel.π b ≫ j.inv
  have : Epi πM := by dsimp [πM]; infer_instance
  have : Epi πN := by dsimp [πN]; infer_instance
  let t := πM ≫ f
  let v := pullback.snd πN t
  have : Epi v := by dsimp [v]; infer_instance
  obtain ⟨U, hU⟩ := AlgebraicGeometry.ProEtale.freeEpiLocalSplitting X R _ _ v ⟨n, ⟨Iso.refl _⟩⟩
  refine ⟨U, fun k => ?_⟩
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f k)).mapMod R
  have : IsSplitEpi (F.map v) := hU k
  let τ := section_ (F.map v) ≫ F.map (pullback.fst πN t)
  have hτ : τ ≫ F.map πN = F.map πM ≫ F.map f := by
    dsimp only [τ]
    rw [Category.assoc, ← F.map_comp, pullback.condition, F.map_comp,
      ← Category.assoc, IsSplitEpi.id, Category.id_comp]
    exact F.map_comp πM f
  let eM := F.mapIso i ≪≫ PreservesCokernel.iso F a
  let eN := F.mapIso j ≪≫ PreservesCokernel.iso F b
  have hπM : F.map πM ≫ eM.hom = cokernel.π (F.map a) := by
    simp [πM, eM]
  have hπN : F.map πN ≫ eN.hom = cokernel.π (F.map b) := by
    simp [πN, eN]
  let φ := eM.inv ≫ F.map f ≫ eN.hom
  have hφ : τ ≫ cokernel.π (F.map b) = cokernel.π (F.map a) ≫ φ := by
    rw [← hπN, ← Category.assoc, hτ]
    simp [φ, ← hπM]
  let δ := biprod.desc (F.map b) τ
  have hfree (n : ℕ) :
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f k)).obj R)
        (F.obj (Mod.finiteFree R n)) :=
    free_pullback (U.f k) ⟨n, ⟨Iso.refl _⟩⟩
  have hfp := fp_cokernel_of_free δ (free_biprod (hfree q) (hfree n)) (hfree p)
  let e : F.obj (cokernel f) ≅ cokernel δ :=
    PreservesCokernel.iso F f ≪≫
      cokernel.mapIso (F.map f) φ eM eN (by simp [φ]) ≪≫
      cokernelPresentationIso (F.map a) (F.map b) φ τ hφ
  exact fp_of_iso hfp e.symm

private lemma common_fp_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M))
    (hN : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) ∧
      Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨V, hV⟩ := hN
  refine ⟨U.bind (fun i ↦ V.pullback₁ (U.f i)), fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  constructor
  · exact (fp_pullback_comp_iff (pullback.fst (U.f i) (V.f j)) (U.f i) M).mpr
      (fp_pullback (pullback.fst (U.f i) (V.f j)) (hU i))
  · change Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).mapMod R).obj N)
    rw [pullback.condition]
    exact (fp_pullback_comp_iff (pullback.snd (U.f i) (V.f j)) (V.f j) N).mpr
      (fp_pullback (pullback.snd (U.f i) (V.f j)) (hV j))

private lemma lfp_cokernel {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : IsLocallyFinitelyPresented R M) (hN : IsLocallyFinitelyPresented R N) :
    IsLocallyFinitelyPresented R (cokernel f) := by
  obtain ⟨U, hU⟩ := common_fp_cover hM hN
  have hv (i : U.I₀) :
      IsLocallyFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj (cokernel f)) := by
    let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
    exact lfp_of_iso (lfp_cokernel_of_fp (F.map f) (hU i).1 (hU i).2)
      (PreservesCokernel.iso F f).symm
  choose V hV using hv
  refine ⟨U.bind V, fun ij => ?_⟩
  rcases ij with ⟨i, j⟩
  exact (fp_pullback_comp_iff ((V i).f j) (U.f i) (cokernel f)).mpr (hV i j)

private lemma constructible_cokernel {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : IsConstructibleModuleObject R M) (hN : IsConstructibleModuleObject R N) :
    IsConstructibleModuleObject R (cokernel f) := by
  obtain ⟨S, hS⟩ := common_lfp_stratification hM hN
  refine ⟨S, fun a => ?_⟩
  let F := (ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R
  exact lfp_of_iso (lfp_cokernel (F.map f) (hS a).1 (hS a).2)
    (PreservesCokernel.iso F f).symm

private lemma fp_biprod_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFinitelyPresented R M) (hN : Mod.IsFree R N) :
    Mod.IsFinitelyPresented R (M ⊞ N) := by
  obtain ⟨n, m, a, ⟨i⟩⟩ := hM
  obtain ⟨p, ⟨j⟩⟩ := hN
  let δ := a ≫ (biprod.inl : Mod.finiteFree R n ⟶
    Mod.finiteFree R n ⊞ Mod.finiteFree R p)
  have h := fp_cokernel_of_free δ ⟨m, ⟨Iso.refl _⟩⟩
    (free_biprod ⟨n, ⟨Iso.refl _⟩⟩ ⟨p, ⟨Iso.refl _⟩⟩)
  exact fp_of_iso h (cokernel_inl_iso a ≪≫ biprod.mapIso i.symm j.symm)

private lemma lfp_extension_of_fp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hQ : Q.ShortExact) (h₁ : Mod.IsFinitelyPresented R Q.X₁)
    (h₃ : Mod.IsFinitelyPresented R Q.X₃) :
    IsLocallyFinitelyPresented R Q.X₂ := by
  obtain ⟨n, m, b, ⟨j⟩⟩ := h₃
  let π := cokernel.π b ≫ j.inv
  have w : b ≫ π = 0 := by simp [π]
  have hp : IsColimit (CokernelCofork.ofπ π w) :=
    IsColimit.ofIsoColimit (cokernelIsCokernel b) (Cofork.ext j.symm (by simp [π]))
  have : Epi Q.g := hQ.epi_g
  let S := ShortComplex.mk
    (pullback.lift (f := Q.g) (g := π) Q.f (0 : Q.X₁ ⟶ Mod.finiteFree R n)
      (by simp))
    (pullback.snd Q.g π) (by simp)
  have hS : S.ShortExact := shortExact_pullback Q hQ π
  let k := pullback.lift (f := Q.g) (g := π) (0 : Mod.finiteFree R m ⟶ Q.X₂) b
    (by simpa using w.symm)
  let e : cokernel k ≅ Q.X₂ := cokernel_pullback_iso b π w hp Q.g
  have : Epi S.g := hS.epi_g
  obtain ⟨U, hU⟩ := AlgebraicGeometry.ProEtale.freeEpiLocalSplitting X R _ _ S.g ⟨n, ⟨Iso.refl _⟩⟩
  have hv (i : U.I₀) :
      IsLocallyFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj Q.X₂) := by
    let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
    have : IsSplitEpi (F.map S.g) := hU i
    have hSF := hS.map_of_exact F
    let split := ShortComplex.Splitting.ofExactOfSection (S.map F) hSF.exact
      (section_ (F.map S.g)) (IsSplitEpi.id _) hSF.mono_f
    have hP : Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (F.obj S.X₂) :=
      fp_of_iso (fp_biprod_free (fp_pullback (U.f i) h₁)
        (free_pullback (U.f i) ⟨n, ⟨Iso.refl _⟩⟩)) split.isoBinaryBiproduct.symm
    have hK : Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (F.obj (Mod.finiteFree R m)) :=
      fp_pullback (U.f i) ⟨m, m, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩
    exact lfp_of_iso (lfp_cokernel_of_fp (F.map k) hK hP)
      ((PreservesCokernel.iso F k).symm ≪≫ F.mapIso e)
  choose V hV using hv
  refine ⟨U.bind V, fun ij => ?_⟩
  rcases ij with ⟨i, j⟩
  exact (fp_pullback_comp_iff ((V i).f j) (U.f i) Q.X₂).mpr (hV i j)

private lemma lfp_extension {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hQ : Q.ShortExact) (h₁ : IsLocallyFinitelyPresented R Q.X₁)
    (h₃ : IsLocallyFinitelyPresented R Q.X₃) :
    IsLocallyFinitelyPresented R Q.X₂ := by
  obtain ⟨U, hU⟩ := common_fp_cover h₁ h₃
  have hv (i : U.I₀) :
      IsLocallyFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj Q.X₂) := by
    let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
    exact lfp_extension_of_fp (Q.map F) (hQ.map_of_exact F) (hU i).1 (hU i).2
  choose V hV using hv
  refine ⟨U.bind V, fun ij => ?_⟩
  rcases ij with ⟨i, j⟩
  exact (fp_pullback_comp_iff ((V i).f j) (U.f i) Q.X₂).mpr (hV i j)

private lemma constructible_extension {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hQ : Q.ShortExact) (h₁ : IsConstructibleModuleObject R Q.X₁)
    (h₃ : IsConstructibleModuleObject R Q.X₃) :
    IsConstructibleModuleObject R Q.X₂ := by
  obtain ⟨S, hS⟩ := common_lfp_stratification h₁ h₃
  refine ⟨S, fun a => ?_⟩
  let F := (ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R
  exact lfp_extension (Q.map F) (hQ.map_of_exact F) (hS a).1 (hS a).2

private lemma constructible_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : IsConstructibleModuleObject R M) (e : M ≅ N) :
    IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a => lfp_of_iso (hS a)
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).mapIso e)⟩

/-- Constructibility by local finite presentations is closed under cokernels and extensions.
Source: finite presentations and local lifting of finitely many generators.
(auxiliary; not a blueprint node)

Proof: refine finite stratifications and presentation covers. For a map of presented
modules, lift the finitely many source generators through the target presentation
locally. The target relations and these lifts give a finite presentation of its
cokernel. For a short exact sequence, pull the sequence back to a finite free
presentation of the quotient. Locally the new free-target epimorphism splits, so its
middle term is a sum of the presented submodule and a finite free module, hence finitely
presented. The original middle term is the cokernel of the map from the finite free
relation module to this pullback. The cokernel argument applies. Exact inverse image
and common refinements put these presentations on all strata. No coefficient
noetherianity is used; zero ranks, zero objects and empty strata are included. -/
theorem constructible_cokernels_extensions (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) ∧
      ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := by
  constructor
  · refine ⟨?_⟩
    intro Y hY
    obtain ⟨f, k, hk, hf⟩ := hY
    exact constructible_of_iso (constructible_cokernel f hf.1 hf.2)
      (colimit.isoColimitCocone ⟨k, hk⟩)
  · exact { prop_X₂_of_shortExact := fun hQ h₁ h₃ => constructible_extension _ hQ h₁ h₃ }

end AlgebraicGeometry.ProEtale.CondensedRing
