/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import WeilConjectures.Mathlib.CategoryTheory.Generator.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# `κ`-generated objects of a Grothendieck abelian category

Let `C` be a Grothendieck abelian category, `G : C` an object and `κ` a cardinal. We say that
an object `X` of `C` is `κ`-generated relative to `G` if there is an epimorphism onto `X` from
a coproduct of strictly fewer than `κ` copies of `G`.

This is the size measure that is used in the construction of K-injective resolutions: unlike
counting subobjects, it is stable under quotients, under joins of `< κ` many subobjects (when
`κ` is regular), and — this is the crucial point — under passing to subobjects, provided `κ`
dominates the countably many cardinals `#(Subobject (G^{⊕n}))` for `n : ℕ`.

## Main definitions and results

- `CategoryTheory.isCardinalGenerated`: the object property of being `κ`-generated.
- `CategoryTheory.isCardinalGenerated_iSup`: stability under joins of `< κ` many subobjects.
- `CategoryTheory.isCardinalGenerated_of_mono`: stability under subobjects.
- `CochainComplex.degreewiseCardinalGenerated`: the degreewise version for cochain complexes,
  together with its stability under quotients and subobjects.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

/-- An object `X` is `κ`-generated relative to `G` if it admits an epimorphism from a
coproduct of fewer than `κ` copies of `G`. -/
def isCardinalGenerated (G : C) (κ : Cardinal.{w}) : ObjectProperty C :=
  fun X ↦ ∃ (ι : Type w) (_ : HasCardinalLT ι κ) (p : (∐ (fun (_ : ι) ↦ G)) ⟶ X), Epi p

lemma isCardinalGenerated_of_epi {X Y : C} (p : X ⟶ Y) [Epi p]
    (hX : isCardinalGenerated G κ X) : isCardinalGenerated G κ Y := by
  obtain ⟨ι, hι, q, hq⟩ := hX
  exact ⟨ι, hι, q ≫ p, epi_comp _ _⟩

instance : (isCardinalGenerated G κ).IsClosedUnderIsomorphisms where
  of_iso e hX := isCardinalGenerated_of_epi G κ e.hom hX

lemma isCardinalGenerated_of_hasCardinalLT_subobject (hG : IsSeparator G) {X : C}
    (hX : HasCardinalLT (Subobject X) κ) : isCardinalGenerated G κ X := by
  classical
  -- the subobjects of `X` which arise as the image of a morphism `G ⟶ X`
  let R : Type max u v := { T : Subobject X // ∃ f : G ⟶ X, imageSubobject f = T }
  have hR : HasCardinalLT R κ := hX.of_injective Subtype.val Subtype.val_injective
  have : Small.{w} R := hR.small
  choose g hg using fun (r : R) ↦ r.2
  refine ⟨Shrink.{w} R, (hasCardinalLT_iff_of_equiv (equivShrink.{w} R) κ).1 hR,
    Sigma.desc (fun s ↦ g ((equivShrink.{w} R).symm s)), ⟨fun {Z} u v huv ↦ ?_⟩⟩
  refine hG.def _ _ fun f ↦ ?_
  obtain ⟨s, hs⟩ : ∃ s, imageSubobject (g ((equivShrink.{w} R).symm s)) = imageSubobject f :=
    ⟨equivShrink.{w} R ⟨imageSubobject f, f, rfl⟩, by rw [Equiv.symm_apply_apply, hg]⟩
  have key : g ((equivShrink.{w} R).symm s) ≫ u = g ((equivShrink.{w} R).symm s) ≫ v := by
    simpa using Sigma.ι (fun (_ : Shrink.{w} R) ↦ G) s ≫= huv
  have h₁ : (imageSubobject f).arrow ≫ u = (imageSubobject f).arrow ≫ v := by
    rw [← hs, ← cancel_epi (factorThruImageSubobject (g ((equivShrink.{w} R).symm s))),
      ← Category.assoc, ← Category.assoc, imageSubobject_arrow_comp]
    exact key
  rw [← imageSubobject_arrow_comp f]
  simp only [Category.assoc, h₁]

lemma isCardinalGenerated_iSup [Fact κ.IsRegular] {X : C} {ι : Type w}
    (S : ι → Subobject X) (hι : HasCardinalLT ι κ)
    (hS : ∀ i, isCardinalGenerated G κ ((S i : C))) :
    isCardinalGenerated G κ ((⨆ i, S i : Subobject X) : C) := by
  choose α hα p hp using hS
  set T : Subobject X := ⨆ i, S i
  refine ⟨Σ (i : ι), α i, hasCardinalLT_sigma' α κ hι hα,
    Sigma.desc (fun x ↦ Sigma.ι (fun (_ : α x.1) ↦ G) x.2 ≫ p x.1 ≫
      Subobject.ofLE (S x.1) T (le_iSup S x.1)), ?_⟩
  refine epi_of_imageSubobject_comp_arrow_eq _ (le_antisymm (imageSubobject_le _ _ rfl) ?_)
  refine iSup_le fun i ↦ ?_
  have hcomp : Sigma.desc (fun (a : α i) ↦ Sigma.ι (fun (_ : Σ (i : ι), α i) ↦ G) ⟨i, a⟩) ≫
      (Sigma.desc (fun x ↦ Sigma.ι (fun (_ : α x.1) ↦ G) x.2 ≫ p x.1 ≫
        Subobject.ofLE (S x.1) T (le_iSup S x.1)) ≫ T.arrow) = p i ≫ (S i).arrow := by
    ext a
    simp
  calc S i = imageSubobject (S i).arrow := by rw [imageSubobject_mono, Subobject.mk_arrow]
    _ = imageSubobject (p i ≫ (S i).arrow) := (imageSubobject_comp_of_epi _ _).symm
    _ ≤ _ := by rw [← hcomp]; exact imageSubobject_comp_le _ _

lemma isCardinalGenerated_of_mono [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G) (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {X Y : C} (f : X ⟶ Y) [Mono f] (hY : isCardinalGenerated G κ Y) :
    isCardinalGenerated G κ X := by
  classical
  obtain ⟨ι, hι, p, hp⟩ := hY
  have := hp
  have : Epi (pullback.fst f p) := Abelian.epi_pullback_of_epi_g f p
  set M : Subobject (∐ fun (_ : ι) ↦ G) := Subobject.mk (pullback.snd f p)
  suffices h : isCardinalGenerated G κ ((M : C)) from
    isCardinalGenerated_of_epi G κ
      ((Subobject.underlyingIso (pullback.snd f p)).hom ≫ pullback.fst f p) h
  -- the directed family of the finite sub-coproducts of `∐ (fun (_ : ι) ↦ G)`
  let j : ∀ (s : Finset ι), (∐ fun (_ : { x : ι // x ∈ s }) ↦ G) ⟶ (∐ fun (_ : ι) ↦ G) :=
    fun s ↦ Sigma.desc (fun x ↦ Sigma.ι (fun (_ : ι) ↦ G) x.1)
  have hj : ∀ (s : Finset ι), IsSplitMono (j s) := fun s ↦
    ⟨⟨Sigma.desc (fun i ↦ if h : i ∈ s then
        Sigma.ι (fun (_ : { x : ι // x ∈ s }) ↦ G) ⟨i, h⟩ else 0), by ext x; simp [j, x.2]⟩⟩
  let F : Finset ι → Subobject (∐ fun (_ : ι) ↦ G) := fun s ↦ Subobject.mk (j s)
  have hFmono : Monotone F := fun s t hst ↦ Subobject.mk_le_mk_of_comm
    (Sigma.desc (fun x ↦ Sigma.ι (fun (_ : { y : ι // y ∈ t }) ↦ G) ⟨x.1, hst x.2⟩))
    (by ext x; simp [j])
  have hFtop : ⨆ (s : Finset ι), F s = ⊤ := by
    have : Epi (⨆ (s : Finset ι), F s).arrow := by
      refine ⟨fun {Z} u v huv ↦ ?_⟩
      ext i
      have hle : F {i} ≤ ⨆ (s : Finset ι), F s := le_iSup F {i}
      have key : Sigma.ι (fun (_ : ι) ↦ G) i =
          (Sigma.ι (fun (_ : { x : ι // x ∈ ({i} : Finset ι) }) ↦ G)
              ⟨i, Finset.mem_singleton_self i⟩ ≫
            (Subobject.underlyingIso (j {i})).inv ≫ Subobject.ofLE _ _ hle) ≫
              (⨆ (s : Finset ι), F s).arrow := by
        simp only [Category.assoc, Subobject.ofLE_arrow]
        rw [show (F {i}).arrow = (Subobject.mk (j {i})).arrow from rfl,
          Subobject.underlyingIso_arrow]
        simp [j]
      rw [key]
      simp only [Category.assoc, huv]
    have : IsIso (⨆ (s : Finset ι), F s).arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow _
  have : Nonempty (Finset ι) := ⟨∅⟩
  have hMeq : M = ⨆ (s : Finset ι), (M ⊓ F s) := by
    rw [← IsGrothendieckAbelian.inf_iSup_of_directed M F
      (fun s t ↦ ⟨s ∪ t, hFmono Finset.subset_union_left, hFmono Finset.subset_union_right⟩),
      hFtop, inf_top_eq]
  have hgen : ∀ (s : Finset ι), isCardinalGenerated G κ (((M ⊓ F s : Subobject _) : C)) := by
    intro s
    refine isCardinalGenerated_of_hasCardinalLT_subobject G κ hG
      (Subobject.hasCardinalLT_of_mono (hsub s.card)
        (Subobject.ofLE _ (F s) inf_le_right ≫ (Subobject.underlyingIso (j s)).hom ≫
          (Sigma.whiskerEquiv s.equivFin (fun _ ↦ Iso.refl G)).hom))
  have := isCardinalGenerated_iSup G κ (fun s ↦ M ⊓ F s) (hasCardinalLT_finset hκ.le hι) hgen
  rwa [← hMeq] at this

end CategoryTheory

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

/-- A cochain complex is degreewise `κ`-generated if each of its components is. -/
def degreewiseCardinalGenerated (G : C) (κ : Cardinal.{w}) :
    ObjectProperty (CochainComplex C ℤ) := fun T ↦ ∀ (n : ℤ), isCardinalGenerated G κ (T.X n)

instance : (degreewiseCardinalGenerated G κ).IsClosedUnderIsomorphisms where
  of_iso e hT n := (isCardinalGenerated G κ).prop_of_iso
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapIso e) (hT n)

lemma degreewiseCardinalGenerated_of_epi {T T' : CochainComplex C ℤ} (p : T ⟶ T')
    [Epi p] (hT : degreewiseCardinalGenerated G κ T) : degreewiseCardinalGenerated G κ T' :=
  fun n ↦ isCardinalGenerated_of_epi G κ (p.f n) (hT n)

lemma degreewiseCardinalGenerated_of_mono [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {T T' : CochainComplex C ℤ} (i : T ⟶ T') [Mono i]
    (hT' : degreewiseCardinalGenerated G κ T') : degreewiseCardinalGenerated G κ T :=
  fun n ↦ isCardinalGenerated_of_mono G κ hκ hG hsub (i.f n) (hT' n)

end CochainComplex
