/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCoverLocalZero
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Testing categorical sheaf epimorphisms by local lifts on finite covers

Source: Stacks Project, Tags 00W1, 00W9 and 00WL, expressed using coefficient
epimorphisms and exact filtered colimits rather than underlying elements.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

private theorem finiteProduct_exact {K : Type} [Finite K]
    (T : K → ShortComplex A) (hT : ∀ k, (T k).Exact) :
    (ShortComplex.mk (Limits.Pi.map fun k ↦ (T k).f) (Limits.Pi.map fun k ↦ (T k).g)
      (by
        apply Pi.hom_ext
        intro k
        simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc, (T k).zero, comp_zero,
          zero_comp])).Exact := by
  let D := (ShortComplex.functorEquivalence (Discrete K) A).inverse.obj
    (Discrete.functor T)
  have hD : D.Exact :=
    (ShortComplex.exact_iff_evaluation D).2 (fun k ↦ hT k.as)
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasExactLimitsOfShape (Discrete K) A :=
    hasExactLimitsOfShape_discrete_finite A
  have hlim := hD.map (lim : (Discrete K ⥤ A) ⥤ A)
  let e₁ : limit D.X₁ ≅ ∏ᶜ (fun k ↦ (T k).X₁) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₁)
  let e₂ : limit D.X₂ ≅ ∏ᶜ (fun k ↦ (T k).X₂) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₂)
  let e₃ : limit D.X₃ ≅ ∏ᶜ (fun k ↦ (T k).X₃) :=
    HasLimit.isoOfNatIso (Discrete.natIso fun k ↦ Iso.refl (T k.as).X₃)
  apply ShortComplex.exact_of_iso (h := hlim)
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

/-- A map out of sections vanishes if it vanishes on every generalized section
admitting local lifts through a sheaf epimorphism on a finite basis cover.
Source: Stacks Project, Tags 00W1, 00W9 and 00WL (the plus construction and local
description of epimorphisms), with Grothendieck abelian coefficients.
(blueprint: stage3-categorical-finite-cover-local-epi).

Proof: The hypothesis applied to restrictions of a global P-section shows that
b annihilates f(V). Thus b descends to the pointwise presheaf cokernel R(V).
Sheafification of R is zero: it preserves the cokernel and sends f to an
epimorphism, after identifying the sheafifications of P and Q with P and Q.
Apply the locally-zero test for R. For a generalized R-section killed by a
finite cover, first lift it to Q(V) after an epimorphism of coefficient objects.
Its restrictions are killed by the presheaf cokernel projections. Finite
products of the pointwise exact cokernel sequences are exact, so after a second
coefficient epimorphism they lift simultaneously to the degree-zero P-cochains.
The hypothesis kills this refined Q-section under b. Cancel the two coefficient
epimorphisms to kill the original R-section under the descended map. The
locally-zero test makes the descended map zero, hence b is zero. -/
theorem hom_eq_zero_of_finite_cover_lifts
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {P Q : Sheaf J A} (f : P ⟶ Q) [Epi f] (V : C) (hV : B V)
    {T : A} (b : Q.obj.obj (op V) ⟶ T)
    (h : ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ {E : A}
        (a : E ⟶ ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P.obj)).X 0)
        (y : E ⟶ Q.obj.obj (op V)),
        a ≫ Limits.Pi.map (fun s : Fin 1 → Fin n ↦
          f.hom.app (op (Presheaf.cechNerveObj U s).left)) =
            y ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ Q.obj) →
        y ≫ b = 0) : b = 0 := by
  obtain ⟨n, U, hUB, _, hU⟩ := hcov V hV ⊤ (J.top_mem V)
  have hb : f.hom.app (op V) ≫ b = 0 := by
    apply h U hUB hU
      (cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P.obj))
      (f.hom.app (op V))
    exact cechAugmentation_naturality U Over.mkIdTerminal
      (Functor.whiskerLeft (Over.forget V).op f.hom)
  let R := cokernel f.hom
  let p : Q.obj ⟶ R := cokernel.π f.hom
  let E := (evaluation Cᵒᵖ A).obj (op V)
  let β : R.obj (op V) ⟶ T :=
    (PreservesCokernel.iso E f.hom).hom ≫ cokernel.desc (f.hom.app (op V)) b hb
  have hpβ : p.app (op V) ≫ β = b := by
    have hp := PreservesCokernel.π_iso_hom E f.hom
    change p.app (op V) ≫ (PreservesCokernel.iso E f.hom).hom =
      cokernel.π (f.hom.app (op V)) at hp
    change p.app (op V) ≫ (PreservesCokernel.iso E f.hom).hom ≫
      cokernel.desc (f.hom.app (op V)) b hb = b
    rw [← Category.assoc, hp, cokernel.π_desc]
  have hR : IsZero ((presheafToSheaf J A).obj R) := by
    have he : Epi ((presheafToSheaf J A).map f.hom) := by
      have he : Epi ((presheafToSheaf J A).map f.hom ≫
          (sheafificationAdjunction J A).counit.app Q) := by
        change Epi ((sheafToPresheaf J A ⋙ presheafToSheaf J A).map f ≫
          (sheafificationAdjunction J A).counit.app Q)
        rw [(sheafificationAdjunction J A).counit.naturality f]
        infer_instance
      exact (epi_comp_iff_of_isIso _ _).1 he
    exact (isZero_cokernel_of_epi ((presheafToSheaf J A).map f.hom)).of_iso
      (PreservesCokernel.iso (presheafToSheaf J A) f.hom)
  have hβ : β = 0 := by
    apply Presheaf.hom_eq_zero_of_sheafification_zero J B hcov R hR V hV β
    intro m W hWB hW D x hx
    have : Epi (p.app (op V)) := by dsimp [p]; infer_instance
    obtain ⟨D', π, hπ, y, hy⟩ := surjective_up_to_refinements_of_epi
      (p.app (op V)) x
    let L := ShortComplex.cokernelSequence f.hom
    have hL : L.Exact := ShortComplex.cokernelSequence_exact f.hom
    have hprod := finiteProduct_exact
      (fun s : Fin 1 → Fin m ↦ L.map
        ((evaluation Cᵒᵖ A).obj (op (Presheaf.cechNerveObj W s).left)))
      (fun s ↦ hL.map _)
    have hzero :
        (y ≫ cechAugmentation W Over.mkIdTerminal ((Over.forget V).op ⋙ Q.obj)) ≫
          Limits.Pi.map (fun s : Fin 1 → Fin m ↦
            p.app (op (Presheaf.cechNerveObj W s).left)) = 0 := by
      have hn := cechAugmentation_naturality W Over.mkIdTerminal
        (Functor.whiskerLeft (Over.forget V).op p)
      change cechAugmentation W Over.mkIdTerminal ((Over.forget V).op ⋙ Q.obj) ≫
        Limits.Pi.map (fun s : Fin 1 → Fin m ↦
          p.app (op (Presheaf.cechNerveObj W s).left)) =
        p.app (op V) ≫ cechAugmentation W Over.mkIdTerminal ((Over.forget V).op ⋙ R) at hn
      rw [Category.assoc, hn, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    obtain ⟨D'', ρ, hρ, a, ha⟩ := hprod.exact_up_to_refinements
      (y ≫ cechAugmentation W Over.mkIdTerminal ((Over.forget V).op ⋙ Q.obj)) hzero
    change ρ ≫ (y ≫ cechAugmentation W Over.mkIdTerminal
      ((Over.forget V).op ⋙ Q.obj)) =
      a ≫ Limits.Pi.map (fun s : Fin 1 → Fin m ↦
        f.hom.app (op (Presheaf.cechNerveObj W s).left)) at ha
    have hab : (ρ ≫ y) ≫ b = 0 := by
      apply h W hWB hW a (ρ ≫ y)
      simpa only [Category.assoc] using ha.symm
    apply (cancel_epi π).1
    apply (cancel_epi ρ).1
    rw [← Category.assoc π x β, hy, Category.assoc y (p.app (op V)) β, hpβ]
    simpa only [Category.assoc, comp_zero] using hab
  rw [← hpβ, hβ, comp_zero]

end CategoryTheory.Sheaf
