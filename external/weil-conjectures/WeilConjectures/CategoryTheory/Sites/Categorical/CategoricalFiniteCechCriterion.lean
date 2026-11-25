/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCechSectionsEpi
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # The finite Čech criterion with Grothendieck abelian coefficients

Source: Stacks Project, Tag 03F9, using the categorical section-lifting lemma.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  {J : GrothendieckTopology C} [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

/-- Positive exactness for all finite covering families with nerve in B. -/
def finiteCechAcyclicOn (B : C → Prop) (F : Sheaf J A) : Prop :=
  ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
    (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) →
    Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
    ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ F.obj)).ExactAt (q + 1)

private theorem finiteProduct_shortExact {K : Type} [Finite K]
    (T : K → ShortComplex A) (hT : ∀ k, (T k).ShortExact) :
    (ShortComplex.mk (Limits.Pi.map fun k ↦ (T k).f) (Limits.Pi.map fun k ↦ (T k).g)
      (by
        apply Pi.hom_ext
        intro k
        simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc, (T k).zero, comp_zero,
          zero_comp])).ShortExact := by
  let D := (ShortComplex.functorEquivalence (Discrete K) A).inverse.obj
    (Discrete.functor T)
  have hD : D.ShortExact := by
    have hf : ∀ k : Discrete K, Mono (D.f.app k) := fun k ↦ (hT k.as).mono_f
    have hg : ∀ k : Discrete K, Epi (D.g.app k) := fun k ↦ (hT k.as).epi_g
    exact ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_evaluation D).2 (fun k ↦ (hT k.as).exact))
      (NatTrans.mono_of_mono_app _) (NatTrans.epi_of_epi_app _)
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasExactLimitsOfShape (Discrete K) A :=
    hasExactLimitsOfShape_discrete_finite A
  have hlim := hD.map_of_exact (lim : (Discrete K ⥤ A) ⥤ A)
  let e₁ : limit D.X₁ ≅ ∏ᶜ (fun k ↦ (T k).X₁) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₁)
  let e₂ : limit D.X₂ ≅ ∏ᶜ (fun k ↦ (T k).X₂) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₂)
  let e₃ : limit D.X₃ ≅ ∏ᶜ (fun k ↦ (T k).X₃) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₃)
  apply ShortComplex.shortExact_of_iso (h := hlim)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · apply Pi.hom_ext
    intro k
    simp only [e₁, e₂, D, Category.assoc, Limits.Pi.map_π,
      ShortComplex.map_f, lim_map, HasLimit.isoOfNatIso_hom_π,
      HasLimit.isoOfNatIso_hom_π_assoc, limMap_π_assoc, Discrete.natIso_hom_app]
    change limit.π D.X₁ ⟨k⟩ ≫ 𝟙 _ ≫ (T k).f =
      limit.π D.X₁ ⟨k⟩ ≫ (T k).f ≫ 𝟙 _
    simp
  · apply Pi.hom_ext
    intro k
    simp only [e₂, e₃, D, Category.assoc, Limits.Pi.map_π,
      ShortComplex.map_g, lim_map, HasLimit.isoOfNatIso_hom_π,
      HasLimit.isoOfNatIso_hom_π_assoc, limMap_π_assoc, Discrete.natIso_hom_app]
    change limit.π D.X₂ ⟨k⟩ ≫ 𝟙 _ ≫ (T k).g =
      limit.π D.X₂ ⟨k⟩ ≫ (T k).g ≫ 𝟙 _
    simp

private noncomputable abbrev sheafFiniteCech {V : C} {n : ℕ} (U : Fin n → Over V) :
    Sheaf J A ⥤ CochainComplex A ℕ :=
  sheafToPresheaf J A ⋙
    (Functor.whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ A).obj (Over.forget V).op ⋙
      cechComplexFunctor U

private instance sheafFiniteCech_additive {V : C} {n : ℕ} (U : Fin n → Over V) :
    (sheafFiniteCech (J := J) (A := A) U).Additive where
  map_add := by
    intro X Y f g
    ext k : 1
    change Limits.Pi.map (fun y : Fin (k + 1) → Fin n ↦
        (f + g).hom.app (op (Presheaf.cechNerveObj U y).left)) =
      Limits.Pi.map (fun y ↦ f.hom.app (op (Presheaf.cechNerveObj U y).left)) +
        Limits.Pi.map (fun y ↦ g.hom.app (op (Presheaf.cechNerveObj U y).left))
    apply Pi.hom_ext
    intro y
    rw [Preadditive.add_comp]
    erw [Limits.Pi.map_π, Limits.Pi.map_π, Limits.Pi.map_π]
    change _ ≫ (f.hom.app _ + g.hom.app _) = _
    rw [Preadditive.comp_add]

private theorem finiteCech_shortExact {S : ShortComplex (Sheaf J A)} (hS : S.ShortExact)
    {V : C} {n : ℕ} (U : Fin n → Over V)
    (hepi : ∀ k (y : Fin (k + 1) → Fin n),
      Epi (S.g.hom.app (op (Presheaf.cechNerveObj U y).left))) :
    (S.map (sheafFiniteCech U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  change (ShortComplex.mk (Limits.Pi.map fun y ↦ S.f.hom.app
      (op (Presheaf.cechNerveObj U y).left))
    (Limits.Pi.map fun y ↦ S.g.hom.app (op (Presheaf.cechNerveObj U y).left)) _).ShortExact
  apply finiteProduct_shortExact
    (fun y : Fin (k + 1) → Fin n ↦ S.map
      (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj
        (op (Presheaf.cechNerveObj U y).left)))
  intro y
  let E := sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj
    (op (Presheaf.cechNerveObj U y).left)
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).1
    inferInstance S hS
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2 (hepi k y)

/-- Categorical finite Čech exactness implies vanishing of positive derived evaluation.
Source: Stacks Project, Tag 03F9.
(blueprint: stage3-categorical-finite-cech-criterion).

Proof: The local section-lifting lemma makes evaluation on B right exact for every
short exact sequence whose first term has positive Čech exactness. Injective sheaves
have this property by the cofree contraction. Every nerve object remains in B, so
finite products of the section sequences form a short exact sequence of Čech complexes.
The homology sequence shows that the cokernel of a monomorphism between two such
sheaves again has positive Čech exactness. The acyclicity criterion for derived functors
now applies to evaluation, which is left exact. Its dimension-shifting induction gives
vanishing in all positive degrees. -/
theorem isZero_rightDerived_eval_of_finiteCech
    [HasInjectiveResolutions (Sheaf J A)]
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (F : Sheaf J A) (hF : finiteCechAcyclicOn B F)
    (V : C) (hV : B V) (q : ℕ) :
    IsZero (((sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op V)).rightDerived
      (q + 1)).obj F) := by
  let E := sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op V)
  apply Functor.rightAcyclic_of_epi_map_g E (finiteCechAcyclicOn B) _ _ _ hF q
  · intro I hI W hW n U hUB hcover k
    have : Injective I.obj := (sheafificationAdjunction J A).map_injective I inferInstance
    exact Presheaf.exactAt_categoricalCech_of_injective I.obj U k
  · intro S hS h₁ h₂ W hW n U hUB hcover k
    have hshort : (S.map (sheafFiniteCech U)).ShortExact :=
      finiteCech_shortExact hS U (fun m y ↦ epi_app_of_finite_cech_exact_one J B hcov hS
        (fun Z hZ _ T hTB hT ↦ h₁ Z hZ T hTB hT 0) _ (hUB m y))
    have h := hshort.homology_exact₃ (k + 1) (k + 2) (by simp)
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h.isZero_X₂_iff.2
      ⟨(h₂ W hW U hUB hcover k).isZero_homology.eq_of_src _ _,
        (h₁ W hW U hUB hcover (k + 1)).isZero_homology.eq_of_tgt _ _⟩
  · intro S hS h₁
    exact epi_app_of_finite_cech_exact_one J B hcov hS
      (fun W hW _ U hUB hcover ↦ h₁ W hW U hUB hcover 0) V hV

end CategoryTheory.Sheaf
