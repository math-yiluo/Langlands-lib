/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonInjectiveVanishingAux
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.Sites.CechCriterion
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Affine vanishing for comparison pullbacks of injective abelian sheaves

Source: Stacks Project, Pro-etale Cohomology, Tag 099U, `lemma-affine-vanishing`
(blueprint: lem-cbc-abelian-affine-comparison-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

theorem affineProEt_cechNerve (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ i, proAffineEtale (U i).left.hom) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    proAffineEtale (Presheaf.cechNerveObj U y).left.hom := by
  let T : Y.AffineProEt := .ofEtale (𝟙 Y)
  have hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun W ↦ MorphismProperty.Over.homMk W.hom) (by
      intro W f
      apply MorphismProperty.Over.Hom.ext
      have hf : f.left ≫ 𝟙 Y = W.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hf)
  let : HasTerminal Y.AffineProEt := hT.hasTerminal
  have : PreservesLimit (Functor.empty Y.AffineProEt)
      (Scheme.AffineProEt.toProEt Y) := by
    apply preservesTerminal_of_iso
    exact (Scheme.AffineProEt.toProEt Y).mapIso
      (terminalIsTerminal.uniqueUpToIso hT) ≪≫
      (MorphismProperty.Over.mkIdTerminal _ Y).uniqueUpToIso terminalIsTerminal
  have : PreservesLimitsOfShape (Discrete PEmpty) (Scheme.AffineProEt.toProEt Y) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesFiniteLimits (Scheme.AffineProEt.toProEt Y) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : HasFiniteLimits Y.AffineProEt := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let X : Y.AffineProEt := .mk V.hom hV
  let W (i : Fin n) : Over X :=
    Over.mk (MorphismProperty.Over.homMk (U i).hom.left (U i).hom.w :
      Scheme.AffineProEt.mk (U i).left.hom (hU i) ⟶ X)
  let G := Over.post (Scheme.AffineProEt.toProEt Y) (X := X)
  let e := PreservesProduct.iso G (fun j : Fin (k + 1) ↦ W (y j))
  have h : proAffineEtale (G.obj (∏ᶜ fun j : Fin (k + 1) ↦ W (y j))).left.hom :=
    (∏ᶜ fun j : Fin (k + 1) ↦ W (y j)).left.prop
  have he : (fun j : Fin (k + 1) ↦ G.obj (W (y j))) =
      (fun j : Fin (k + 1) ↦ U (y j)) := by rfl
  rw [he] at e
  have hw : e.inv.left.left ≫
      (G.obj (∏ᶜ fun j : Fin (k + 1) ↦ W (y j))).left.hom =
        (Presheaf.cechNerveObj U y).left.hom := by simp
  rw [← hw, proAffineEtale.cancel_left_of_respectsIso]
  exact h

theorem affineProEt_finite_refinement (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology Y V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, proAffineEtale (U i).left.hom) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
        Scheme.ProEt.topology Y V := by
  classical
  let X : Y.AffineProEt := .mk V.hom hV
  let F := Scheme.AffineProEt.toProEt Y
  have hr : R.functorPullback F (X := X) ∈ Scheme.AffineProEt.topology Y X :=
    F.cover_lift _ _ hR
  obtain ⟨ι, hι, W, f, hf, hsurj⟩ :=
    Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hr
  let := hι
  let := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let U (i : Fin (Fintype.card ι)) : Over V := Over.mk (F.map (f (e i)))
  refine ⟨Fintype.card ι, U, fun i ↦ (W (e i)).prop, fun i ↦ hf (e i), ?_⟩
  apply Precoverage.generate_mem_toGrothendieck
  change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
    Scheme.ProEt.precoverage Y V
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  let D : PreZeroHypercover V.left :=
    ⟨Fin (Fintype.card ι), fun i ↦ (W (e i)).left, fun i ↦ (f (e i)).left⟩
  have hs : ∀ x : V.left, ∃ i, x ∈ Set.range (D.f i) := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨e.symm i, ?_⟩
    change x ∈ Set.range (f (e (e.symm i))).left
    rw [e.apply_symm_apply]
    exact ⟨y, hy⟩
  have : ∀ i, IsAffine (D.X i) := fun i ↦ (W (e i)).prop.isAffine
  have : IsAffine V.left := hV.isAffine
  have hD : QuasiCompactCover D :=
    ⟨fun {O} hO ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (D.f i).isSpectralMap) (fun x _ ↦ hs x) O.2 hO.isCompact⟩
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2
      ⟨hs, fun i ↦ by
        change WeaklyEtale (f (e i)).left
        infer_instance⟩⟩

end AlgebraicGeometry.ProEtale
