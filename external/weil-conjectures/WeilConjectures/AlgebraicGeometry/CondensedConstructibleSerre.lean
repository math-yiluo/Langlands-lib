/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields

import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality

/-!
# Serre closure for constructible condensed field module sheaves

Source: upstream `ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`, Sorried input;
Bhatt--Scholze, Section 6.8, Lemma 6.8.7 and Corollary 6.8.9
(auxiliary; not a blueprint node).

The coefficients are pulled back from condensed abelian groups. Algebraic-closure sections
have image in a single finite intermediate field, as in `Profinite.padicAlgClRingObj`.
Constructibility is stratified local finite presentation, with no completeness condition.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj in
private lemma fp_of_iso {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)] {M N : Mod C R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_of_iso {A : Type v} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (h : IsLocallyFinitelyPresented R M) (e : M ≅ N) :
    IsLocallyFinitelyPresented R N := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun i ↦ fp_of_iso (hU i) (((upperStar A (U.f i)).mapMod R).mapIso e)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  apply fp_map ((upperStar Ab.{u + 1} g).mapMod R) _ h
  exact Mod.isoMk (Iso.refl _) (by simp [Mod.act])

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented S M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  apply fp_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : Mod.IsFree S (F.obj M) := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨F.mapIso i ≪≫ F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e)⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) :
    Mod.IsFree ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  exact free_map ((upperStar Ab.{u + 1} g).mapMod R)
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) h

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  apply free_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree S M := by
  exact free_of_iso (free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_cokernel_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : Mod.IsFree R M) (hN : Mod.IsFree R N) :
    Mod.IsFinitelyPresented R (cokernel f) := by
  obtain ⟨m, ⟨i⟩⟩ := hM
  obtain ⟨n, ⟨j⟩⟩ := hN
  let f' := i.inv ≫ f ≫ j.hom
  exact ⟨n, m, f', ⟨cokernel.mapIso f f' i j (by simp [f'])⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def kernelIsoCokernelOfSection
    {C : Type*} [Category C] [Abelian C] {M N : C}
    (f : M ⟶ N) (s : N ⟶ M) (hs : s ≫ f = 𝟙 N) :
    kernel f ≅ cokernel (f ≫ s) := by
  let p : M ⟶ kernel f := kernel.lift f (𝟙 M - f ≫ s) (by simp [hs])
  have hp : (f ≫ s) ≫ p = 0 := by
    apply (cancel_mono (kernel.ι f)).1
    simp [p, Preadditive.comp_sub, reassoc_of% hs]
  refine
    { hom := kernel.ι f ≫ cokernel.π (f ≫ s)
      inv := cokernel.desc (f ≫ s) p hp
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono (kernel.ι f)).1
    simp [p, Preadditive.comp_sub]
  · apply (cancel_epi (cokernel.π (f ≫ s))).1
    simp [p, Preadditive.sub_comp]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_kernel_of_section {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (f : M ⟶ N) (s : N ⟶ M) (hs : s ≫ f = 𝟙 N) (hM : Mod.IsFree R M) :
    Mod.IsFinitelyPresented R (kernel f) :=
  fp_of_iso (fp_cokernel_of_free (f ≫ s) hM hM)
    (kernelIsoCokernelOfSection f s hs).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def finiteFreeBiprodIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] (m n : ℕ) :
    Mod.finiteFree R m ⊞ Mod.finiteFree R n ≅ Mod.finiteFree R (m + n) := by
  let A := Mod.regular R
  refine
    { hom := biprod.desc
        (biproduct.desc fun i : Fin m ↦ biproduct.ι (fun _ : Fin (m + n) ↦ A)
          (Fin.castAdd n i))
        (biproduct.desc fun j : Fin n ↦ biproduct.ι (fun _ : Fin (m + n) ↦ A)
          (Fin.natAdd m j))
      inv := biproduct.desc (Fin.addCases
        (fun i : Fin m ↦ biproduct.ι (fun _ : Fin m ↦ A) i ≫ biprod.inl)
        (fun j : Fin n ↦ biproduct.ι (fun _ : Fin n ↦ A) j ≫ biprod.inr))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro i <;> simp [A]
  · apply biproduct.hom_ext'
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [A]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_biprod {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) (hN : Mod.IsFree R N) : Mod.IsFree R (M ⊞ N) := by
  obtain ⟨m, ⟨i⟩⟩ := hM
  obtain ⟨n, ⟨j⟩⟩ := hN
  exact ⟨m + n, ⟨biprod.mapIso i j ≪≫ finiteFreeBiprodIso R m n⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) : Mod.IsFinitelyPresented R M := by
  obtain ⟨n, ⟨i⟩⟩ := hM
  exact ⟨n, n, 0, ⟨i ≪≫ cokernelZeroIsoTarget.symm⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Mod.IsFree ((upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFree ((upperStar Ab.{u + 1} f).obj ((upperStar Ab.{u + 1} g).obj R))
      (((upperStar Ab.{u + 1} f).mapMod _).obj
        (((upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar Ab.{u + 1} g
  let G := upperStar Ab.{u + 1} f
  let e := upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ free_of_iso (free_comap φ h) i.symm,
    fun h ↦ free_of_comap φ (free_of_iso h i)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma common_free_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M))
    (hN : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) ∧
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨V, hV⟩ := hN
  refine ⟨U.bind (fun i ↦ V.pullback₁ (U.f i)), fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  constructor
  · exact (free_pullback_comp_iff (pullback.fst (U.f i) (V.f j)) (U.f i) M).mpr
      (free_pullback (pullback.fst (U.f i) (V.f j)) (hU i))
  · change Mod.IsFree
      ((upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).obj R)
      (((upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).mapMod R).obj N)
    rw [pullback.condition]
    exact (free_pullback_comp_iff (pullback.snd (U.f i) (V.f j)) (V.f j) N).mpr
      (free_pullback (pullback.snd (U.f i) (V.f j)) (hV j))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_cokernel_of_locally_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N)
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M))
    (hN : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N)) :
    IsLocallyFinitelyPresented R (cokernel f) := by
  obtain ⟨U, hU⟩ := common_free_cover hM hN
  refine ⟨U, fun i ↦ ?_⟩
  let F := (upperStar Ab.{u + 1} (U.f i)).mapMod R
  exact fp_of_iso (fp_cokernel_of_free (F.map f) (hU i).1 (hU i).2)
    (PreservesCokernel.iso F f).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def ccsUnitPresheafLift {W : Scheme.{u}}
    {G : W.ProEtᵒᵖ ⥤ Ab.{u + 1}} (x : G.obj (op (⊤_ W.ProEt))) :
    𝟙_ (W.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ G where
  app U := AddCommGrpCat.ofHom {
    toFun n := n.down • G.map (terminal.from U.unop).op x
    map_zero' := zero_zsmul _
    map_add' a b := add_zsmul _ _ _ }
  naturality U U' f := by
    ext n
    change n.down • G.map (terminal.from U'.unop).op x =
      G.map f (n.down • G.map (terminal.from U.unop).op x)
    rw [map_zsmul, ← ConcreteCategory.comp_apply, ← G.map_comp,
      show (terminal.from U.unop).op ≫ f = (terminal.from U'.unop).op from
        Quiver.Hom.unop_inj (terminal.hom_ext _ _)]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccsUnitPresheafLift_one {W : Scheme.{u}}
    {G : W.ProEtᵒᵖ ⥤ Ab.{u + 1}} (x : G.obj (op (⊤_ W.ProEt))) :
    (ccsUnitPresheafLift x).app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} ℤ) = x := by
  change (1 : ℤ) • G.map (terminal.from _).op x = x
  rw [one_zsmul, terminal.hom_ext (terminal.from (⊤_ W.ProEt)) (𝟙 _), op_id, G.map_id]
  rfl

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccsUnitPresheaf_hom_ext {W : Scheme.{u}}
    {G : W.ProEtᵒᵖ ⥤ Ab.{u + 1}}
    {a b : 𝟙_ (W.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ G}
    (h : a.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} ℤ) =
      b.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} ℤ)) : a = b := by
  have key (c : 𝟙_ (W.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ G) :
      c = ccsUnitPresheafLift (c.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} ℤ)) := by
    ext U n
    change c.app U n = n.down • G.map (terminal.from U.unop).op
      (c.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} ℤ))
    rw [← ConcreteCategory.comp_apply, ← c.naturality]
    change c.app U n = n.down • c.app U (1 : ULift.{u + 1} ℤ)
    rw [← map_zsmul]
    exact congrArg (c.app U) (ULift.ext (by
      change n.down = n.down * 1
      exact (_root_.mul_one _).symm))
  rw [key a, key b, h]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def ccsUnitSheafLift {W : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}}
    (x : F.obj.obj (op (⊤_ W.ProEt))) : 𝟙_ _ ⟶ F :=
  inv (Functor.OplaxMonoidal.η (presheafToSheaf (Scheme.ProEt.topology W) Ab.{u + 1})) ≫
    ((sheafificationAdjunction _ _).homEquiv _ _).symm (ccsUnitPresheafLift x)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_ε_comp_unitSheafLift {W : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}}
    (x : F.obj.obj (op (⊤_ W.ProEt))) :
    ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map (ccsUnitSheafLift x) =
      ccsUnitPresheafLift x := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology W) Ab.{u + 1}).homEquiv
    _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm]
  have : ((sheafificationAdjunction (Scheme.ProEt.topology W)
      Ab.{u + 1}).homEquiv _ _).symm (ε (sheafToPresheaf _ _)) =
        Functor.OplaxMonoidal.η (presheafToSheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :=
    Equiv.symm_apply_apply _ _
  rw [this, ccsUnitSheafLift, IsIso.hom_inv_id_assoc]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_exists_cover_unit_lift {V : Scheme.{u}}
    {P Q : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}}
    (q : P ⟶ Q) [Epi q] (τ : 𝟙_ _ ⟶ Q) :
    ∃ R ∈ Scheme.proetalePrecoverage V, ∀ ⦃W : Scheme.{u}⦄ (g : W ⟶ V), R g →
      ∃ (hg : WeaklyEtale g) (σ : 𝟙_ _ ⟶
        ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          Ab.{u + 1} (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).obj P),
        σ ≫ ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          Ab.{u + 1} (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).map q =
        ε _ ≫ ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          Ab.{u + 1} (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).map τ := by
  let T : V.ProEt := Scheme.ProEt.mk (𝟙 V)
  let y : Q.obj.obj (op T) :=
    (ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map τ).app (op T)
      (1 : ULift.{u + 1} ℤ)
  have hq : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := q)).2 inferInstance
  have hS := Presheaf.imageSieve_mem (Scheme.ProEt.topology V) q.hom (U := op T) y
  rw [Scheme.ProEt.mem_topology_iff] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨idx, Z, φ, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (φ i).left) ∈
      Scheme.proetalePrecoverage V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hR
    exact hR
  refine ⟨_, hR', ?_⟩
  rintro _ _ ⟨i⟩
  have hw := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR' (.mk i)
  obtain ⟨x, hx⟩ := hle _ (φ i) (Presieve.ofArrows.mk i)
  let TW := ⊤_ (Z i).left.ProEt
  let k : (MorphismProperty.Over.map ⊤ hw).obj TW ⟶ Z i :=
    MorphismProperty.Over.homMk TW.hom (by
      have := MorphismProperty.Over.w (φ i)
      rw [← this]
      exact congrArg (TW.hom ≫ ·) (Category.comp_id _))
  refine ⟨hw, ccsUnitSheafLift (P.obj.map k.op x), ?_⟩
  apply Sheaf.hom_ext_of_ε_comp
  apply ccsUnitPresheaf_hom_ext
  rw [Functor.map_comp, reassoc_of% ccs_ε_comp_unitSheafLift, Functor.map_comp, NatTrans.comp_app,
    ConcreteCategory.comp_apply, ccsUnitPresheafLift_one]
  simp only [NatTrans.comp_app]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  change q.hom.app _ (P.obj.map k.op x) = τ.hom.app _
    ((ε (sheafToPresheaf (Scheme.ProEt.topology V) Ab.{u + 1})).app _
      (1 : ULift.{u + 1} ℤ))
  rw [NatTrans.naturality_apply, hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [y]
  erw [← NatTrans.naturality_apply (ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map τ)]
  rfl

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_localization_unit_app {V X : Scheme.{u}} (g : V ⟶ X)
    (h : WeaklyEtale g) (P : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (U : X.ProEtᵒᵖ) :
    ((sheafToPresheaf _ Ab.{u + 1}).map
      ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g h).unit.app P)).app U =
      P.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g h trivial).counit.app
        U.unop).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_localization_unit {V X : Scheme.{u}} (g : V ⟶ X) (h : WeaklyEtale g) :
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g h).unit.app (𝟙_ _) =
      ε (lowerStar Ab.{u + 1} g) ≫ (lowerStar Ab.{u + 1} g).map
        (ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
          Ab.{u + 1} (Scheme.ProEt.topology V) (Scheme.ProEt.topology X))) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, ccs_localization_unit_app]
  erw [← (ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})).naturality]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ h)]
  erw [Monoidal.tensorUnit_map, Category.id_comp]
  rfl

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_comparison_unit {V X : Scheme.{u}} (g : V ⟶ X) (h : WeaklyEtale g) :
    ε (upperStar Ab.{u + 1} g) ≫
        (upperStarIsoLocalizationRestriction Ab.{u + 1} g h).hom.app (𝟙_ _) =
      ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
        Ab.{u + 1} (Scheme.ProEt.topology V) (Scheme.ProEt.topology X)) := by
  rw [← cancel_epi (Functor.OplaxMonoidal.η (upperStar Ab.{u + 1} g))]
  simp only [Functor.Monoidal.η_ε_assoc]
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
  dsimp only [upperStarIsoLocalizationRestriction]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_app_unit_comp_map_η]
  exact ccs_localization_unit g h

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def ccsRegularMapIso {V X : Scheme.{u}} (g : V ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    ((upperStar Ab.{u + 1} g).mapMod R).obj (Mod.regular R) ≅
      Mod.regular ((upperStar Ab.{u + 1} g).obj R) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma ccs_exists_cover_regular_lift {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (q : M ⟶ N) [Epi q] (t : Mod.regular R ⟶ N) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      ∃ s : Mod.regular ((upperStar Ab.{u + 1} (U.f i)).obj R) ⟶
        ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M,
        s ≫ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).map q =
          (ccsRegularMapIso (U.f i) R).inv ≫
            ((upperStar Ab.{u + 1} (U.f i)).mapMod R).map t := by
  have : Epi q.hom := (Mod.forget R).map_epi q
  obtain ⟨S, hS, h⟩ :=
    ccs_exists_cover_unit_lift q.hom ((MonObj.one : 𝟙_ _ ⟶ R) ≫ t.hom)
  obtain ⟨idx, Z, g, rfl⟩ := S.exists_eq_ofArrows
  let U : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
    { I₀ := idx, X := Z, f := g, mem₀ := hS }
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine ⟨U.restrictIndexOfSmall.{u}, fun j ↦ ?_⟩
  let i := Precoverage.ZeroHypercover.Small.restrictFun U j
  obtain ⟨hw, σ, hσ⟩ := h (g i) (.mk i)
  let e : upperStar Ab.{u + 1} (g i) ≅
      (MorphismProperty.Over.map ⊤ hw).sheafPushforwardContinuous
        Ab.{u + 1} (Scheme.ProEt.topology (Z i)) (Scheme.ProEt.topology X) :=
    upperStarIsoLocalizationRestriction Ab.{u + 1} (g i) hw
  change ∃ s : Mod.regular ((upperStar Ab.{u + 1} (g i)).obj R) ⟶
      ((upperStar Ab.{u + 1} (g i)).mapMod R).obj M,
      s ≫ ((upperStar Ab.{u + 1} (g i)).mapMod R).map q =
        (ccsRegularMapIso (g i) R).inv ≫
          ((upperStar Ab.{u + 1} (g i)).mapMod R).map t
  refine ⟨Mod.regularLift (((upperStar Ab.{u + 1} (g i)).mapMod R).obj M)
    (σ ≫ e.inv.app M.X), ?_⟩
  apply Mod.regular_hom_ext
  change (MonObj.one : 𝟙_ _ ⟶ (upperStar Ab.{u + 1} (g i)).obj R) ≫
      (Mod.regularLift (((upperStar Ab.{u + 1} (g i)).mapMod R).obj M)
        (σ ≫ e.inv.app M.X)).hom ≫
        (upperStar Ab.{u + 1} (g i)).map q.hom =
      (MonObj.one : 𝟙_ _ ⟶ (upperStar Ab.{u + 1} (g i)).obj R) ≫
        (upperStar Ab.{u + 1} (g i)).map t.hom
  rw [← Category.assoc, Mod.one_comp_regularLift, Category.assoc, ← e.inv.naturality,
    reassoc_of% hσ, e.inv.naturality, ← Category.assoc]
  have hε : ε ((MorphismProperty.Over.map ⊤ hw).sheafPushforwardContinuous
      Ab.{u + 1} (Scheme.ProEt.topology (Z i)) (Scheme.ProEt.topology X)) ≫
        e.inv.app (𝟙_ _) = ε (upperStar Ab.{u + 1} (g i)) := by
    rw [← ccs_comparison_unit (g i) hw, Category.assoc, e.hom_inv_id_app,
      Category.comp_id]
  rw [hε, Functor.map_comp]
  rfl

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private abbrev FreeEpiLocalSplitting : Prop :=
  ∀ (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (f : M ⟶ N) [Epi f], Mod.IsFree R N →
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      IsSplitEpi (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map f)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma freeEpiLocalSplitting : FreeEpiLocalSplitting.{u} := by
  intro X R _ _ M N q _ hN
  obtain ⟨n, ⟨e⟩⟩ := hN
  obtain ⟨U, hU⟩ := ccs_exists_cover_regular_lift
    (biproduct.map fun _ : Fin n ↦ q)
    (biproduct.lift fun k ↦ biproduct.ι (fun _ : Fin n ↦ Mod.regular R) k ≫ e.inv)
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨s, hs⟩ := hU i
  let F := (upperStar Ab.{u + 1} (U.f i)).mapMod R
  let σ : Mod.finiteFree ((upperStar Ab.{u + 1} (U.f i)).obj R) n ⟶ F.obj M :=
    biproduct.desc fun k ↦ s ≫ F.map (biproduct.π _ k)
  let τ : Mod.finiteFree ((upperStar Ab.{u + 1} (U.f i)).obj R) n ⟶ F.obj N :=
    biproduct.map (fun _ : Fin n ↦ (ccsRegularMapIso (U.f i) R).inv) ≫
      (F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R)).inv ≫ F.map e.inv
  have hτ : σ ≫ F.map q = τ := by
    refine biproduct.hom_ext' _ _ fun k ↦ ?_
    simp only [σ, τ, biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_map_assoc,
      Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Functor.map_comp]
    rw [show biproduct.π (fun _ : Fin n ↦ M) k ≫ q =
        biproduct.map (fun _ : Fin n ↦ q) ≫ biproduct.π _ k by simp,
      Functor.map_comp, reassoc_of% hs, ← Functor.map_comp,
      biproduct.lift_π, Functor.map_comp]
  have : IsIso (biproduct.map fun _ : Fin n ↦ (ccsRegularMapIso (U.f i) R).inv) :=
    (biproduct.mapIso fun _ ↦ (ccsRegularMapIso (U.f i) R).symm).isIso_hom
  have : IsIso τ := by dsimp only [τ]; infer_instance
  exact ⟨⟨inv τ ≫ σ, by rw [Category.assoc, hτ, IsIso.inv_hom_id]⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact fp_of_iso (fp_comap (F.map φ) (hU i)) ((F.mapModComapIso φ).app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma locally_free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) (e : M ≅ N) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N) := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun i ↦ free_of_iso (hU i)
    (((upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma locally_free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj S)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod S).obj M)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj ((Mod.comap φ).obj M)) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact free_of_iso (free_comap (F.map φ) (hU i)) ((F.mapModComapIso φ).app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma locally_free_pullback_coeff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y] (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((upperStar Ab.{u + 1} g).obj (condensedRingObj Λ X)))
    (hP : IsLocallyFinitelyPresented _ P) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} g).obj (condensedRingObj Λ X)))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod _).obj P) := by
  let φ := condensedPullbackHom Λ g
  exact locally_free_of_iso
    (locally_free_comap φ (hLF Y _ (lfp_comap (inv φ) hP)))
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app P)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented R ((Mod.comap φ).obj M)) :
    Mod.IsFinitelyPresented S M := by
  exact fp_of_iso (fp_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented R ((Mod.comap φ).obj M)) :
    IsLocallyFinitelyPresented S M := by
  exact lfp_of_iso (lfp_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} f).obj
      ((upperStar Ab.{u + 1} g).obj R))
      (((upperStar Ab.{u + 1} f).mapMod _).obj
        (((upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar Ab.{u + 1} g
  let G := upperStar Ab.{u + 1} f
  let e := upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ fp_of_iso (fp_comap φ h) i.symm,
    fun h ↦ fp_of_comap φ (fp_of_iso h i)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_kernel_epi_of_locally_free (hsplit : FreeEpiLocalSplitting.{u})
    {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f : M ⟶ N) [Epi f]
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M))
    (hN : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N)) :
    IsLocallyFinitelyPresented R (kernel f) := by
  classical
  obtain ⟨U, hU⟩ := common_free_cover hM hN
  have hv (i : U.I₀) := hsplit (U.X i) _ _ _
    (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map f) (hU i).2
  choose V hV using hv
  refine ⟨U.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  let F := (upperStar Ab.{u + 1} (U.f i)).mapMod R
  let G := (upperStar Ab.{u + 1} ((V i).f j)).mapMod
    ((upperStar Ab.{u + 1} (U.f i)).obj R)
  have : IsSplitEpi (G.map (F.map f)) := hV i j
  apply (fp_pullback_comp_iff ((V i).f j) (U.f i) (kernel f)).mpr
  exact fp_of_iso
    (fp_kernel_of_section (G.map (F.map f)) (section_ (G.map (F.map f)))
      (IsSplitEpi.id _) (free_pullback ((V i).f j) (hU i).1))
    (PreservesKernel.iso (F ⋙ G) f).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.pullback₁ g, fun i ↦ ?_⟩
  change Mod.IsFinitelyPresented _
    (((upperStar Ab.{u + 1} (pullback.fst g (U.f i))).mapMod _).obj _)
  apply (fp_pullback_comp_iff (pullback.fst g (U.f i)) g M).mp
  rw [pullback.condition]
  exact (fp_pullback_comp_iff (pullback.snd g (U.f i)) (U.f i) M).mpr
    (fp_pullback (pullback.snd g (U.f i)) (hU i))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} f).obj
      ((upperStar Ab.{u + 1} g).obj R))
      (((upperStar Ab.{u + 1} f).mapMod _).obj
        (((upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar Ab.{u + 1} g
  let G := upperStar Ab.{u + 1} f
  let e := upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ lfp_of_iso (lfp_comap φ h) i.symm,
    fun h ↦ lfp_of_comap φ (lfp_of_iso h i)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma common_lfp_stratification {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : IsConstructibleModuleObject R M) (hN : IsConstructibleModuleObject R N) :
    ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M) ∧
      IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj N) := by
  obtain ⟨S, hS⟩ := hM
  obtain ⟨V, hV⟩ := hN
  refine ⟨S.inter V, fun a ↦ ?_⟩
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  constructor
  · exact (lfp_pullback_comp_iff (pullback.fst (S.immersion i) (V.immersion j))
      (S.immersion i) M).mpr
      (lfp_pullback (pullback.fst (S.immersion i) (V.immersion j)) (hS i))
  · change IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} (pullback.fst (S.immersion i) (V.immersion j) ≫
        S.immersion i)).obj R)
      (((upperStar Ab.{u + 1} (pullback.fst (S.immersion i) (V.immersion j) ≫
        S.immersion i)).mapMod R).obj N)
    rw [pullback.condition]
    exact (lfp_pullback_comp_iff (pullback.snd (S.immersion i) (V.immersion j))
      (V.immersion j) N).mpr
      (lfp_pullback (pullback.snd (S.immersion i) (V.immersion j)) (hV j))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_serre_of_locally_free (hsplit : FreeEpiLocalSplitting.{u})
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (hLF : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      IsLocallyFinitelyPresented R M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
          (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsLocallyFinitelyPresented R M → IsLocallyFinitelyPresented R N →
      IsLocallyFinitelyPresented R (kernel f) ∧ IsLocallyFinitelyPresented R (cokernel f)) ∧
    (∀ Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      Q.ShortExact → IsLocallyFinitelyPresented R Q.X₁ →
      IsLocallyFinitelyPresented R Q.X₃ → IsLocallyFinitelyPresented R Q.X₂) := by
  constructor
  · intro M N f hM hN
    have hC := lfp_cokernel_of_locally_free f (hLF M hM) (hLF N hN)
    have hI' : IsLocallyFinitelyPresented R (Abelian.image f) :=
      lfp_kernel_epi_of_locally_free hsplit (cokernel.π f) (hLF N hN) (hLF _ hC)
    have hI := lfp_of_iso hI' (Abelian.imageIsoImage f)
    have hK := lfp_kernel_epi_of_locally_free hsplit (factorThruImage f)
      (hLF M hM) (hLF _ hI)
    exact ⟨lfp_of_iso hK (kernelFactorThruImage f), hC⟩
  · intro Q hQ h₁ h₃
    classical
    have : Epi Q.g := hQ.epi_g
    obtain ⟨U, hU⟩ := common_free_cover (hLF _ h₁) (hLF _ h₃)
    have hv (i : U.I₀) := hsplit (U.X i) _ _ _
      (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map Q.g) (hU i).2
    choose V hV using hv
    refine ⟨U.bind V, fun ij ↦ ?_⟩
    rcases ij with ⟨i, j⟩
    let F := (upperStar Ab.{u + 1} (U.f i)).mapMod R
    let G := (upperStar Ab.{u + 1} ((V i).f j)).mapMod
      ((upperStar Ab.{u + 1} (U.f i)).obj R)
    have : IsSplitEpi (G.map (F.map Q.g)) := hV i j
    have hQ' := hQ.map_of_exact (F ⋙ G)
    let t := ShortComplex.Splitting.ofExactOfSection (Q.map (F ⋙ G)) hQ'.exact
      (section_ (G.map (F.map Q.g))) (IsSplitEpi.id _) hQ'.mono_f
    apply (fp_pullback_comp_iff ((V i).f j) (U.f i) Q.X₂).mpr
    exact fp_of_free (free_of_iso
      (free_biprod (free_pullback ((V i).f j) (hU i).1)
        (free_pullback ((V i).f j) (hU i).2)) t.isoBinaryBiproduct.symm)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma constructible_serre_of_lfp_serre {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hlocal : ∀ (S : Scheme.Stratification X) (a : Fin S.n),
      let R' := (upperStar Ab.{u + 1} (S.immersion a)).obj R
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1}) R')
        (f : M ⟶ N), IsLocallyFinitelyPresented R' M → IsLocallyFinitelyPresented R' N →
        IsLocallyFinitelyPresented R' (kernel f) ∧
          IsLocallyFinitelyPresented R' (cokernel f)) ∧
      (∀ Q : ShortComplex
        (Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1}) R'),
        Q.ShortExact → IsLocallyFinitelyPresented R' Q.X₁ →
        IsLocallyFinitelyPresented R' Q.X₃ → IsLocallyFinitelyPresented R' Q.X₂)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f)) ∧
    (∀ Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      Q.ShortExact → IsConstructibleModuleObject R Q.X₁ →
      IsConstructibleModuleObject R Q.X₃ → IsConstructibleModuleObject R Q.X₂) := by
  constructor
  · intro M N f hM hN
    obtain ⟨S, hS⟩ := common_lfp_stratification hM hN
    refine ⟨⟨S, fun a ↦ ?_⟩, ⟨S, fun a ↦ ?_⟩⟩
    · let F := (upperStar Ab.{u + 1} (S.immersion a)).mapMod R
      exact lfp_of_iso ((hlocal S a).1 _ _ (F.map f) (hS a).1 (hS a).2).1
        (PreservesKernel.iso F f).symm
    · let F := (upperStar Ab.{u + 1} (S.immersion a)).mapMod R
      exact lfp_of_iso ((hlocal S a).1 _ _ (F.map f) (hS a).1 (hS a).2).2
        (PreservesCokernel.iso F f).symm
  · intro Q hQ h₁ h₃
    obtain ⟨S, hS⟩ := common_lfp_stratification h₁ h₃
    refine ⟨S, fun a ↦ ?_⟩
    let F := (upperStar Ab.{u + 1} (S.immersion a)).mapMod R
    exact (hlocal S a).2 (Q.map F) (hQ.map_of_exact F) (hS a).1 (hS a).2

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma condensed_constructible_serre_of_locally_free
    (hsplit : FreeEpiLocalSplitting.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : M ⟶ N), IsConstructibleModuleObject (condensedRingObj Λ X) M →
      IsConstructibleModuleObject (condensedRingObj Λ X) N →
      IsConstructibleModuleObject (condensedRingObj Λ X) (kernel f) ∧
      IsConstructibleModuleObject (condensedRingObj Λ X) (cokernel f)) ∧
    (∀ Q : ShortComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Q.ShortExact → IsConstructibleModuleObject (condensedRingObj Λ X) Q.X₁ →
      IsConstructibleModuleObject (condensedRingObj Λ X) Q.X₃ →
      IsConstructibleModuleObject (condensedRingObj Λ X) Q.X₂) := by
  apply constructible_serre_of_lfp_serre
  intro S a
  have : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  exact lfp_serre_of_locally_free hsplit _
    (locally_free_pullback_coeff Λ hLF (S.immersion a))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def liftCoefficientIso (E : Type) [TopologicalSpace E] [Ring E]
    [IsTopologicalRing E] :
    Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E) where
  hom := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv.symm : E ≃+* ULift.{u} E).toRingHom.compLeftContinuous
        S.unop continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  inv := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv : ULift.{u} E ≃+* E).toRingHom.compLeftContinuous
        S.unop continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma finite_lf (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsLocallyFinitelyPresented (padicSubfieldRingObj X ℓ E) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (padicSubfieldRingObj X ℓ E))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (padicSubfieldRingObj X ℓ E)).obj M) := by
  let E' := ULift.{u} E.val
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro S a b
        apply ULift.ext
        change (a.down * b.down : C(S.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E.val)
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (liftCoefficientIso E.val).hom
  have : IsMonHom φ := inferInstance
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv φ)).obj M) (lfp_comap (inv φ) hM)
  exact locally_free_of_iso (locally_free_comap φ h)
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app M)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma algcl_lf (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsLocallyFinitelyPresented (padicAlgClRingObj X ℓ) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (padicAlgClRingObj X ℓ))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (padicAlgClRingObj X ℓ)).obj M) := by
  obtain ⟨U, hU⟩ := condensedQbar_lfp_locally_free ℓ X M hM
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (U.f i)
  have h : Mod.IsFree _ ((Mod.comap (inv φ)).obj
      (((upperStar Ab.{u + 1} (U.f i)).mapMod (padicAlgClRingObj X ℓ)).obj M)) := by
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  exact free_of_comap (inv φ) h

/-- Kernels, cokernels and extensions of constructible modules over the finite intermediate field
coefficient sheaf are constructible.
Source: upstream ProEtaleModule/DerivedCategory.lean, Sorried input; Bhatt--Scholze 6.8.7,
6.8.9 (auxiliary; not a blueprint node).

Proof: coefficient pullback comparisons identify restriction with inverse image with an
invertible coefficient map. Exact abelian inverse image and exact forgetfulness therefore
make restriction exact and preserve finite presentations and free modules. Base change
preserves weakly etale arrows and fpqc coverings, so presentation covers restrict along
arbitrary stratum immersions. Refine the two finite stratifications by their scheme fibre
products; the images are intersections (affine locally Spec of the quotient by the sum of
the two ideals), and their spaces remain noetherian. On each stratum, local finite
presentation implies pro-etale local finite freeness, using the finite-field and
algebraic-closure local-triviality lemmas respectively. Combine finitely many covers.
For a matrix between finite free modules its cokernel has a finite presentation; trivialize
this globally defined cokernel and lift its finitely many basis sections locally. This
splits the quotient of the target, and its image is presented as the cokernel of the
complement of the resulting idempotent. Trivialize that globally defined image and lift
its basis into the source. If t splits the source-to-image map p, the kernel is the
cokernel of tp on the finite free source, so is locally finitely presented. For an extension,
trivialize the outer terms and lift the quotient basis locally; this splits the extension
as their direct sum. Exact restriction identifies these constructions with the global
kernel, cokernel and middle term on each stratum. Thus the refined stratification proves
all three conclusions. Local triviality is applied only on the noetherian strata, never
on arbitrary covering schemes. Empty schemes, empty strata and rank zero require no basis
lifts and satisfy the same formulas. -/
theorem isConstructibleModuleObject_serre_padicSubfield
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicSubfieldRingObj T ℓ E)) (f : M ⟶ N),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) N →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) (kernel f) ∧
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicSubfieldRingObj T ℓ E)),
      S.ShortExact →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₁ →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₃ →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₂) := by
  exact condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousMapRingObj E.val) (finite_lf ℓ E) T

/-- Kernels, cokernels and extensions of constructible modules over the bounded-image
algebraic-closure coefficient sheaf are constructible.
Source: upstream ProEtaleModule/DerivedCategory.lean, Sorried input; Bhatt--Scholze 6.8.7,
6.8.9 (auxiliary; not a blueprint node).

Proof: coefficient pullback comparisons identify restriction with inverse image with an
invertible coefficient map. Exact abelian inverse image and exact forgetfulness therefore
make restriction exact and preserve finite presentations and free modules. Base change
preserves weakly etale arrows and fpqc coverings, so presentation covers restrict along
arbitrary stratum immersions. Refine the two finite stratifications by their scheme fibre
products; the images are intersections (affine locally Spec of the quotient by the sum of
the two ideals), and their spaces remain noetherian. On each stratum, local finite
presentation implies pro-etale local finite freeness, using the finite-field and
algebraic-closure local-triviality lemmas respectively. Combine finitely many covers.
For a matrix between finite free modules its cokernel has a finite presentation; trivialize
this globally defined cokernel and lift its finitely many basis sections locally. This
splits the quotient of the target, and its image is presented as the cokernel of the
complement of the resulting idempotent. Trivialize that globally defined image and lift
its basis into the source. If t splits the source-to-image map p, the kernel is the
cokernel of tp on the finite free source, so is locally finitely presented. For an extension,
trivialize the outer terms and lift the quotient basis locally; this splits the extension
as their direct sum. Exact restriction identifies these constructions with the global
kernel, cokernel and middle term on each stratum. Thus the refined stratification proves
all three conclusions. Local triviality is applied only on the noetherian strata, never
on arbitrary covering schemes. Empty schemes, empty strata and rank zero require no basis
lifts and satisfy the same formulas. -/
theorem isConstructibleModuleObject_serre_padicAlgCl
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicAlgClRingObj T ℓ)) (f : M ⟶ N),
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) N →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) (kernel f) ∧
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicAlgClRingObj T ℓ)),
      S.ShortExact →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₁ →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₃ →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₂) := by
  exact condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.padicAlgClRingObj ℓ) (algcl_lf ℓ) T

end AlgebraicGeometry.ProEtale
