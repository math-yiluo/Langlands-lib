/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.PerfectClosedImmersion
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.AlgebraicGeometry.AffineQuotientResolutionSheafification
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeResolutionPerfectModel

/-!
# Koszul-regular closed immersions are perfect

Source: Stacks Project, More on Morphisms, Lemma 37.61.7, Tag 068C
(blueprint: lem-sc-koszul-regular-closed-immersion-perfect).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed immersion locally cut out by finite Koszul-regular sequences has a local
Koszul resolution by finite free modules, is a perfect closed immersion, and its
pushed-forward structure sheaf is perfect in `D(𝒪_Y)`.
Source: Stacks Project, Tag 068C, Lemma 37.61.7
(blueprint: lem-sc-koszul-regular-closed-immersion-perfect).

Proof: (1) On an affine open `U`, the quotient-spectrum identification of
`def-weil-closed-immersion` identifies the restricted pushforward with the sheaf
associated to `A/I`. (2) `def-weil-pbc-koszul-regular-sequence` gives vanishing of
positive Koszul homology. In degree zero, the differential of
`def-weil-pbc-koszul-complex` has image `I`, so the augmentation to `A/I` is a
quasi-isomorphism. Exactness of sheafification preserves this quasi-isomorphism.
(3) Exterior-power bases make the Koszul terms finite free, and terms above the
length vanish. The resulting local strictly perfect representatives give
`lemma-coherent-base-change-invertible-sheaves--1`. (4) These bounded finite free quotient
resolutions satisfy `def-sc-perfect-closed-immersion`. No Noetherian hypothesis is required. -/
theorem koszulRegular_closedImmersion_perfect {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      ∃ (I : Ideal (Γ(Y, U))) (r : ℕ) (f : Fin r → Γ(Y, U)),
        I = Ideal.span (Set.range f) ∧ RingTheory.Sequence.IsKoszulRegular f ∧
        ∃ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
            Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
          i ∣_ U ≫ U.toSpecΓ =
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (∀ (U : Y.Opens) (hU : IsAffineOpen U),
      ∀ (I : Ideal (Γ(Y, U))) (r : ℕ) (f : Fin r → Γ(Y, U)),
        I = Ideal.span (Set.range f) → RingTheory.Sequence.IsKoszulRegular f →
        ∀ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
            Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
          i ∣_ U ≫ U.toSpecΓ =
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) →
          (∃ q : ((tilde.functor Γ(Y, U) ⋙
                Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
                  (ComplexShape.down ℕ)).obj
                    (ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f) ⟶
              (ChainComplex.single₀ U.toScheme.Modules).obj
                ((Scheme.Modules.restrictFunctor U.ι).obj
                  ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            QuasiIso q) ∧
          (∀ n : ℕ, Module.Free (Γ(Y, U) : Type u)
              ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n) ∧
            Module.Finite (Γ(Y, U) : Type u)
              ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n)) ∧
          (∀ n : ℕ, r < n →
            IsZero ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n))) ∧
    IsPerfectClosedImmersion i ∧
    Scheme.IsPerfect Y
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) := by
  have hterms (U : Y.Opens) (r : ℕ) (f : Fin r → Γ(Y, U)) (n : ℕ) :
      Module.Free (Γ(Y, U) : Type u)
          ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n) ∧
        Module.Finite (Γ(Y, U) : Type u)
          ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n) := by
    change Module.Free (Γ(Y, U) : Type u) (⋀[Γ(Y, U)]^n (Fin r →₀ Γ(Y, U))) ∧
      Module.Finite (Γ(Y, U) : Type u) (⋀[Γ(Y, U)]^n (Fin r →₀ Γ(Y, U)))
    exact ⟨inferInstance, inferInstance⟩
  have hzero (U : Y.Opens) (r : ℕ) (f : Fin r → Γ(Y, U)) (n : ℕ) (hn : r < n) :
      IsZero ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n) := by
    classical
    change IsZero (ModuleCat.of (Γ(Y, U) : Type u)
      (⋀[Γ(Y, U)]^n (Fin r →₀ Γ(Y, U))))
    let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) (Γ(Y, U) : Type u)
      (Fin r →₀ Γ(Y, U))).exteriorPower n
    have hempty : IsEmpty (Set.powersetCard (Fin r) n) := by
      refine ⟨fun s ↦ ?_⟩
      have hcard := Finset.card_le_univ s.val
      simp only [Fintype.card_fin] at hcard
      exact (Nat.not_le_of_gt hn) (s.prop ▸ hcard)
    let hsub : Subsingleton (⋀[Γ(Y, U)]^n (Fin r →₀ Γ(Y, U))) :=
      b.repr.toEquiv.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have haug (U : Y.Opens) (I : Ideal (Γ(Y, U))) (r : ℕ)
      (f : Fin r → Γ(Y, U)) (hf : I = Ideal.span (Set.range f))
      (hr : RingTheory.Sequence.IsKoszulRegular f) :
      ∃ ε : ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f ⟶
          (ChainComplex.single₀ (ModuleCat (Γ(Y, U) : Type u))).obj
            (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)), QuasiIso ε := by
    obtain ⟨ε, hε, _⟩ := ExteriorAlgebra.exists_koszul_quotient_augmentation
      (Γ(Y, U) : Type u) I r f hr hf.symm
    let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)) 0 0 (by simp)
    let ε' := (ComplexShape.embeddingDownNat.fullyFaithfulExtendFunctor
      (ModuleCat (Γ(Y, U) : Type u))).preimage (ε ≫ e.inv)
    refine ⟨ε', ?_⟩
    apply (HomologicalComplex.quasiIso_extendMap_iff ε'
      ComplexShape.embeddingDownNat).mp
    have hm : HomologicalComplex.extendMap ε' ComplexShape.embeddingDownNat =
        ε ≫ e.inv := (ComplexShape.embeddingDownNat.fullyFaithfulExtendFunctor
          (ModuleCat (Γ(Y, U) : Type u))).map_preimage _
    rw [hm]
    let := hε
    infer_instance
  have hres (U : Y.Opens) (I : Ideal (Γ(Y, U))) (r : ℕ)
      (f : Fin r → Γ(Y, U)) (hf : I = Ideal.span (Set.range f))
      (hr : RingTheory.Sequence.IsKoszulRegular f) :
      ∃ P : ProjectiveResolution
          (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)),
        P.complex = ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f := by
    obtain ⟨ε, hε⟩ := haug U I r f hf hr
    let P : ProjectiveResolution
        (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)) :=
      { complex := ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f
        projective := fun n ↦ by
          let := (hterms U r f n).1
          change Projective (ModuleCat.of (Γ(Y, U) : Type u)
            (⋀[Γ(Y, U)]^n (Fin r →₀ Γ(Y, U))))
          infer_instance
        π := ε
        quasiIso := hε }
    exact ⟨P, rfl⟩
  have hlocal : ∀ (U : Y.Opens) (hU : IsAffineOpen U)
      (I : Ideal (Γ(Y, U))) (r : ℕ) (f : Fin r → Γ(Y, U)),
      I = Ideal.span (Set.range f) → RingTheory.Sequence.IsKoszulRegular f →
      ∀ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
          Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
        i ∣_ U ≫ U.toSpecΓ =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) →
        ∃ q : ((tilde.functor Γ(Y, U) ⋙
              Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
                (ComplexShape.down ℕ)).obj
                  (ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f) ⟶
            (ChainComplex.single₀ U.toScheme.Modules).obj
              ((Scheme.Modules.restrictFunctor U.ι).obj
                ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
          QuasiIso q := by
    intro U hU I r f hf hr e he
    obtain ⟨ε, hε⟩ := haug U I r f hf hr
    let := hε
    exact exists_affine_quotient_sheafified_resolution i U hU I e he _ ε
  refine ⟨?_, ?_, ?_⟩
  · intro U hU I r f hf hr e he
    exact ⟨hlocal U hU I r f hf hr e he, hterms U r f, hzero U r f⟩
  · intro y
    obtain ⟨U, hy, hU, I, r, f, hf, hr, e, he⟩ := h y
    obtain ⟨P, hP⟩ := hres U I r f hf hr
    refine ⟨U, hy, hU, I, ⟨e, he⟩, P, ?_, ?_, r + 1, ?_⟩
    · intro n
      rw [hP]
      exact (hterms U r f n).2
    · intro n
      rw [hP]
      let := (hterms U r f n).1
      infer_instance
    · intro n hn
      rw [hP]
      exact hzero U r f n (Nat.lt_of_succ_le hn)
  · intro y
    obtain ⟨U, hy, hU, I, r, f, hf, hr, e, he⟩ := h y
    obtain ⟨q, hq⟩ := hlocal U hU I r f hf hr e he
    let := hq
    obtain ⟨L, hL, eL⟩ := exists_affine_finite_free_perfect_model U hU
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
      (ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f) r
      (fun n ↦ (hterms U r f n).1) (fun n ↦ (hterms U r f n).2)
      (hzero U r f) q
    exact ⟨U, hy, L, hL, eL⟩

end AlgebraicGeometry
