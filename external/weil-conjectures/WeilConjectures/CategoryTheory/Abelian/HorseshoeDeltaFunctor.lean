/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.CategoryTheory.DeltaFunctor
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLift

/-!
# Horseshoe connecting morphisms for right derived functors

Source: Weibel, *An Introduction to Homological Algebra*, Theorem 2.4.6 and
Lemma 2.2.8; Stacks Project, Derived Categories, Tags 013T and 0117
(blueprint: lem-weil-pbc-horseshoe-delta-functor).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]

private structure Horseshoe (S : ShortComplex A) where
  IA : InjectiveResolution S.X₁
  IB : InjectiveResolution S.X₂
  IC : InjectiveResolution S.X₃
  α : IA.cocomplex ⟶ IB.cocomplex
  β : IB.cocomplex ⟶ IC.cocomplex
  zero : α ≫ β = 0
  augA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι
  augB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι
  rows : ∀ k : ℕ, ((ShortComplex.mk α β zero).map
    (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact

private theorem horseshoe_exists (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (Horseshoe S) := by
  obtain ⟨IA, IB, IC, α, β, hα, hβ, hz, hr⟩ :=
    InjectiveResolution.exists_horseshoe_resolutions S hS
  exact ⟨⟨IA, IB, IC, α, β, hz, hα, hβ, fun k ↦ (hr k).1⟩⟩

private noncomputable def chosenHorseshoe (S : ShortComplex A) (hS : S.ShortExact) :
    Horseshoe S := Classical.choice (horseshoe_exists S hS)

omit [EnoughInjectives A] in
private theorem horseshoe_map_exact (v : A ⥤ B) [v.Additive]
    {S : ShortComplex A} (H : Horseshoe S) :
    ((ShortComplex.mk H.α H.β H.zero).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  have hr := H.rows k
  change (ShortComplex.mk (H.α.f k) (H.β.f k) _).ShortExact at hr
  exact (hr.splittingOfInjective.map v).shortExact

private noncomputable def horseshoeBoundary (v : A ⥤ B) [v.Additive]
    {S : ShortComplex A} (H : Horseshoe S) (n : ℕ) :
    (v.rightDerived n).obj S.X₃ ⟶ (v.rightDerived (n + 1)).obj S.X₁ :=
  (H.IC.isoRightDerivedObj v n).hom ≫
    (horseshoe_map_exact v H).δ n (n + 1) rfl ≫
      (H.IA.isoRightDerivedObj v (n + 1)).inv

private theorem horseshoeBoundary_naturality (v : A ⥤ B) [v.Additive]
    (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact)
    (H : Horseshoe S) (K : Horseshoe T) (f : S ⟶ T) (n : ℕ) :
    horseshoeBoundary v H n ≫ (v.rightDerived (n + 1)).map f.τ₁ =
      (v.rightDerived n).map f.τ₃ ≫ horseshoeBoundary v K n := by
  let a := InjectiveResolution.desc f.τ₁ K.IA H.IA
  let c := InjectiveResolution.desc f.τ₃ K.IC H.IC
  have ha := InjectiveResolution.desc_commutes f.τ₁ K.IA H.IA
  have hc := InjectiveResolution.desc_commutes f.τ₃ K.IC H.IC
  obtain ⟨b, _, hab, hbc⟩ := InjectiveResolution.exists_horseshoe_morphism_lift
    S T hS hT f H.IA H.IB H.IC K.IA K.IB K.IC H.α H.β K.α K.β
    H.zero K.zero H.augA H.augB K.augA K.augB H.rows K.rows a c ha hc
  let t : ShortComplex.mk H.α H.β H.zero ⟶ ShortComplex.mk K.α K.β K.zero :=
    { τ₁ := a, τ₂ := b, τ₃ := c, comm₁₂ := hab.symm, comm₂₃ := hbc }
  have hd := HomologicalComplex.HomologySequence.δ_naturality
    ((v.mapHomologicalComplex (ComplexShape.up ℕ)).mapShortComplex.map t)
    (horseshoe_map_exact v H) (horseshoe_map_exact v K) n (n + 1) rfl
  have hna := H.IA.isoRightDerivedObj_inv_naturality f.τ₁ K.IA a
    (InjectiveResolution.desc_commutes_zero f.τ₁ K.IA H.IA) v (n + 1)
  have hnc := H.IC.isoRightDerivedObj_hom_naturality f.τ₃ K.IC c
    (InjectiveResolution.desc_commutes_zero f.τ₃ K.IC H.IC) v n
  change (horseshoe_map_exact v H).δ n (n + 1) rfl ≫
    (v.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ (n + 1)).map a =
    (v.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map c ≫
      (horseshoe_map_exact v K).δ n (n + 1) rfl at hd
  dsimp only [horseshoeBoundary]
  simp only [Category.assoc]
  rw [hna]
  simp only [← Category.assoc]
  rw [hnc]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ (H.IC.isoRightDerivedObj v n).hom ≫ z ≫
      (K.IA.isoRightDerivedObj v (n + 1)).inv) hd

private theorem transport_exact {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
    (hf : f ≫ e₂.hom = e₁.hom ≫ f') (hg : g ≫ e₃.hom = e₂.hom ≫ g')
    (hz : f' ≫ g' = 0) (he : (ShortComplex.mk f' g' hz).Exact) :
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact := by
  have h : f ≫ g = 0 := by
    rw [← cancel_mono e₃.hom, Category.assoc, hg, ← Category.assoc, hf,
      Category.assoc, hz, zero_comp, comp_zero]
  refine ⟨h, ?_⟩
  exact ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm).symm he

private theorem horseshoeBoundary_exact (v : A ⥤ B) [v.Additive]
    {S : ShortComplex A} (H : Horseshoe S) (n : ℕ) :
    (∃ h : (v.rightDerived n).map S.f ≫ (v.rightDerived n).map S.g = 0,
      (ShortComplex.mk ((v.rightDerived n).map S.f)
        ((v.rightDerived n).map S.g) h).Exact) ∧
    (∃ h : (v.rightDerived n).map S.g ≫ horseshoeBoundary v H n = 0,
      (ShortComplex.mk ((v.rightDerived n).map S.g) (horseshoeBoundary v H n) h).Exact) ∧
    (∃ h : horseshoeBoundary v H n ≫ (v.rightDerived (n + 1)).map S.f = 0,
      (ShortComplex.mk (horseshoeBoundary v H n)
        ((v.rightDerived (n + 1)).map S.f) h).Exact) := by
  have hα (k : ℕ) := v.rightDerived_map_eq k S.f H.α H.augA
  have hβ (k : ℕ) := v.rightDerived_map_eq k S.g H.β H.augB
  have ca (k : ℕ) : (v.rightDerived k).map S.f ≫ (H.IB.isoRightDerivedObj v k).hom =
      (H.IA.isoRightDerivedObj v k).hom ≫
        HomologicalComplex.homologyMap ((v.mapHomologicalComplex _).map H.α) k := by
    rw [hα k]
    simp only [Category.assoc, Iso.inv_hom_id, comp_id, Functor.comp_map,
      HomologicalComplex.homologyFunctor_map]
  have cb (k : ℕ) : (v.rightDerived k).map S.g ≫ (H.IC.isoRightDerivedObj v k).hom =
      (H.IB.isoRightDerivedObj v k).hom ≫
        HomologicalComplex.homologyMap ((v.mapHomologicalComplex _).map H.β) k := by
    rw [hβ k]
    simp only [Category.assoc, Iso.inv_hom_id, comp_id, Functor.comp_map,
      HomologicalComplex.homologyFunctor_map]
  have cd : horseshoeBoundary v H n ≫ (H.IA.isoRightDerivedObj v (n + 1)).hom =
      (H.IC.isoRightDerivedObj v n).hom ≫
        (horseshoe_map_exact v H).δ n (n + 1) rfl := by
    simp only [horseshoeBoundary, Category.assoc, Iso.inv_hom_id, comp_id]
  exact ⟨transport_exact (H.IA.isoRightDerivedObj v n) (H.IB.isoRightDerivedObj v n)
      (H.IC.isoRightDerivedObj v n) _ _ _ _ (ca n) (cb n) _
      ((horseshoe_map_exact v H).homology_exact₂ n),
    transport_exact (H.IB.isoRightDerivedObj v n) (H.IC.isoRightDerivedObj v n)
      (H.IA.isoRightDerivedObj v (n + 1)) _ _ _ _ (cb n) cd _
      ((horseshoe_map_exact v H).homology_exact₃ n (n + 1) rfl),
    transport_exact (H.IC.isoRightDerivedObj v n) (H.IA.isoRightDerivedObj v (n + 1))
      (H.IB.isoRightDerivedObj v (n + 1)) _ _ _ _ cd (ca (n + 1)) _
      ((horseshoe_map_exact v H).homology_exact₁ n (n + 1) rfl)⟩

private theorem horseshoe_mono_zero (v : A ⥤ B) [v.Additive]
    {S : ShortComplex A} (H : Horseshoe S) : Mono ((v.rightDerived 0).map S.f) := by
  let α := (v.mapHomologicalComplex (ComplexShape.up ℕ)).map H.α
  have hr := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (horseshoe_map_exact v H) 0
  have : Mono (α.f 0) := hr.mono_f
  have : Mono (HomologicalComplex.homologyMap α 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel α 0 (by
      intro i hi
      change i + 1 = 0 at hi
      omega)
  rw [v.rightDerived_map_eq 0 S.f H.α H.augA]
  change Mono ((H.IA.isoRightDerivedObj v 0).hom ≫
    HomologicalComplex.homologyMap α 0 ≫ (H.IB.isoRightDerivedObj v 0).inv)
  infer_instance

/-- The connecting morphisms obtained from every compatible (horseshoe) injective
resolution make the right derived functors into a cohomological delta-functor.
The comparison equation identifies `G.delta` with the snake-lemma boundary for every
horseshoe, transported by `isoRightDerivedObj`. The `eqToHom` maps only identify the
objects of `G.F` with the objects of `v.rightDerived` using `hF`. Thus `G.naturality`
gives naturality for any two horseshoes, and the identity ladder gives independence.

Source: Weibel, Theorem 2.4.6 with Lemma 2.2.8; Stacks Project, Derived Categories,
Tag 013T and Homology, Tags 0117 and 010Q.
(blueprint: lem-weil-pbc-horseshoe-delta-functor)

Proof:
1. Choose injective resolutions and lifts of two maps. Their sum lifts the sum of the
maps. Additivity of `v` and homology, with the comparison rule of
lem-weil-pbc-derived-functor-map-via-lift, gives additivity of each right derived functor
(lem-weil-pbc-left-exact-injective-resolution-degree-zero,
lem-weil-pbc-injective-resolution-lift-exists).
2. Each horseshoe row splits since its first object is injective: extend its identity
across the first map and factor the complementary projection through the cokernel.
Additivity preserves the splitting identities, so applying `v` gives short exact rows.
The snake lemma defines the cohomology boundary; transport it by `isoRightDerivedObj`
(lem-weil-pbc-complex-ses-homology-long-exact, def-sp-injective-resolutions).
3. Lift a morphism of short exact sequences to the endpoint resolutions and use
lem-weil-pbc-horseshoe-morphism-lift for the middle map. Apply `v` and naturality of the
homology boundary (lem-weil-pbc-complex-ses-long-exact-naturality). The comparison rule
of lem-weil-pbc-derived-functor-map-via-lift yields naturality of the transported maps.
4. Apply Step 3 to the identity morphism between two horseshoes of the same sequence.
The right derived functors preserve identities, so the transported maps are equal.
5. Choose a horseshoe (lem-weil-pbc-injective-resolution-ses) and transport its long
exact cohomology sequence using lem-weil-pbc-derived-functor-map-via-lift. The zeroth
cohomology is a kernel, since the complexes vanish in negative degrees; its first map
is monic because the degree-zero horseshoe map is split monic. Thus the sequence is
exact including the initial zero (lem-weil-pbc-complex-ses-homology-long-exact).
6. Package additivity, exactness, and naturality as the delta-functor of
def-weil-pbc-delta-functor. Step 4 identifies its boundary with that of every horseshoe.
-/
theorem exists_horseshoe_rightDerived_deltaFunctor
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] :
    ∃ (G : CohomologicalDeltaFunctor A B)
      (hF : G.F = (fun n : ℕ ↦ v.rightDerived n)),
      ∀ (S : ShortComplex A) (hS : S.ShortExact)
        (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
        (IC : InjectiveResolution S.X₃)
        (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
        (hαβ : α ≫ β = 0)
        (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
        (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
        (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact),
        ∃ hvH : ((ShortComplex.mk α β hαβ).map
          (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact,
          ∀ n : ℕ,
            G.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) =
              eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫
                (IC.isoRightDerivedObj v n).hom ≫ hvH.δ n (n + 1) rfl ≫
                  (IA.isoRightDerivedObj v (n + 1)).inv := by
  classical
  let G : CohomologicalDeltaFunctor A B :=
    { F := fun n ↦ v.rightDerived n
      additive := fun n ↦ inferInstance
      delta := fun S hS n ↦ horseshoeBoundary v (chosenHorseshoe S hS) n
      mono_zero := fun S hS ↦ horseshoe_mono_zero v (chosenHorseshoe S hS)
      exact_middle := fun S hS n ↦ (horseshoeBoundary_exact v (chosenHorseshoe S hS) n).1
      exact_right := fun S hS n ↦ (horseshoeBoundary_exact v (chosenHorseshoe S hS) n).2.1
      exact_left := fun S hS n ↦ (horseshoeBoundary_exact v (chosenHorseshoe S hS) n).2.2
      naturality := fun S T hS hT f n ↦ horseshoeBoundary_naturality v S T hS hT
        (chosenHorseshoe S hS) (chosenHorseshoe T hT) f n }
  refine ⟨G, rfl, ?_⟩
  intro S hS IA IB IC α β hz ha hb hr
  let H : Horseshoe S := ⟨IA, IB, IC, α, β, hz, ha, hb, hr⟩
  refine ⟨horseshoe_map_exact v H, ?_⟩
  intro n
  have hn := horseshoeBoundary_naturality v S S hS hS (chosenHorseshoe S hS) H (𝟙 S) n
  simpa [G, horseshoeBoundary, H] using hn

end CategoryTheory
