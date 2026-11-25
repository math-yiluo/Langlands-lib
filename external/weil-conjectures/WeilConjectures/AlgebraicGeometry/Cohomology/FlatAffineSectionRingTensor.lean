/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The section ring of a cartesian affine open

Source: Stacks Project, Tags 01I4 and 02KG.
(blueprint: lem-pc-flat-affine-section-ring-tensor)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}}

/-- The affine cartesian ring formula, with both coefficient maps fixed.
Source: Stacks Project, Tag 01I4, Lemma 26.6.7, applied to the affine open;
Tag 02KG, proof of Lemma 30.5.1.
(blueprint: lem-pc-flat-affine-section-ring-tensor)

Proof: Restrict the base-change square to W. Its upper left corner is the
inverse-image open W', and it is still cartesian. Identify W with Spec A by
its canonical affine-open isomorphism. Naturality identifies its structure
map with Spec of the displayed R-algebra map. The affine pullback formula
identifies W' with Spec (A tensor_R S), and its projection formulas identify
the maps from A and S with the two tensor inclusions. Applying global
sections and the canonical global-sections isomorphism of Spec gives the
A-algebra equivalence. The S-projection formula gives its value on 1 tensor b.
This also covers the empty open: A and its base-change ring are zero rings. -/
theorem exists_baseChange_affine_sectionRing_tensor (f : X ⟶ Spec (.of R))
    (W : X.Opens) (hW : IsAffineOpen W)
    (W' : (baseChangedScheme (S := S) f).Opens)
    (hW' : W' = baseChangeFst (S := S) f ⁻¹ᵁ W)
    (h : W' ≤ baseChangeFst (S := S) f ⁻¹ᵁ W) :
    let α := ((X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let β := (((baseChangedScheme (S := S) f).presheaf.map
      (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    letI : Algebra R Γ(X, W) := α.toAlgebra
    letI : Algebra Γ(X, W) Γ(baseChangedScheme (S := S) f, W') :=
      (baseChangeFst (S := S) f |>.appLE W W' h).hom.toAlgebra
    ∃ e : (Γ(X, W) ⊗[R] S) ≃ₐ[Γ(X, W)] Γ(baseChangedScheme (S := S) f, W'),
      ∀ b : S, e (1 ⊗ₜ[R] b) = β b := by
  dsimp only
  let α := ((X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom).comp
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let β := (((baseChangedScheme (S := S) f).presheaf.map
    (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let : Algebra R Γ(X, W) := α.toAlgebra
  let : Algebra Γ(X, W) Γ(baseChangedScheme (S := S) f, W') :=
    (baseChangeFst (S := S) f |>.appLE W W' h).hom.toAlgebra
  have H := IsPullback.of_hasPullback f (baseChangeMap R S)
  have hUST : (⊤ : (Spec (.of S)).Opens) ≤ baseChangeMap R S ⁻¹ᵁ ⊤ := by simp
  have hUSX : W ≤ f ⁻¹ᵁ ⊤ := by simp
  have hUY : W' = baseChangeFst (S := S) f ⁻¹ᵁ W ⊓
      baseChangeSnd (S := S) f ⁻¹ᵁ ⊤ := by simpa using hW'
  -- Affine opens in a cartesian square give a pushout of section rings.
  have hp := (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
      (isAffineOpen_top _) (isAffineOpen_top _) hW)
  -- Identify the global sections of the two base spectra with R and S.
  have hp' : IsPushout (CommRingCat.ofHom α)
      (CommRingCat.ofHom (algebraMap R S))
      (baseChangeFst (S := S) f |>.appLE W W' h) (CommRingCat.ofHom β) := by
    refine hp.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
      (Scheme.ΓSpecIso (.of S)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [α, Scheme.Hom.appTop, Scheme.Hom.appLE, Category.assoc]
    · simp [Scheme.Hom.appLE, baseChangeMap,
        Scheme.ΓSpecIso_naturality]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp [β, Scheme.Hom.appTop, Scheme.Hom.appLE, Category.assoc]
      rfl
  -- The unique pushout isomorphism respects both tensor inclusions.
  let ht := CommRingCat.isPushout_tensorProduct R Γ(X, W) S
  let ei := ht.isoIsPushout _ _ hp'
  let er := ei.commRingCatIsoToRingEquiv
  have ha (a : Γ(X, W)) : er (a ⊗ₜ[R] (1 : S)) =
      (baseChangeFst (S := S) f |>.appLE W W' h).hom a := by
    exact ConcreteCategory.congr_hom (ht.inl_isoIsPushout_hom _ _ hp') a
  have hb (b : S) : er (1 ⊗ₜ[R] b) = β b := by
    exact ConcreteCategory.congr_hom (ht.inr_isoIsPushout_hom _ _ hp') b
  let e : (Γ(X, W) ⊗[R] S) ≃ₐ[Γ(X, W)] Γ(baseChangedScheme (S := S) f, W') :=
    { er with commutes' := ha }
  exact ⟨e, hb⟩

end AlgebraicGeometry.Scheme.Modules
