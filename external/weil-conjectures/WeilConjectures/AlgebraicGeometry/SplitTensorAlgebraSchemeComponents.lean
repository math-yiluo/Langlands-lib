/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.SplitReductionSpectrumComponents
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme components from a split reduced tensor algebra

Source: smooth purity blueprint, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Convert a specified reduced tensor product decomposition into open scheme components.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation.
(blueprint: lem-weil-pbc-split-tensor-algebra-scheme-components).

Proof: Identify the affine schemes with spectra of their global sections, compatibly
with g. Identify the principal open with Spec of the localization away from c, and
use the specified finite étale surjective algebra to construct its cover Spec A'.
The affine tensor product formula identifies the pullback source with Spec of the
specified tensor algebra. The given algebra isomorphism identifies its reduction
with the spectrum of the finite product. The factor spectra are open and closed,
pairwise disjoint, and cover that spectrum, including when r = 0. Reduction is a
surjective closed immersion and a homeomorphism, so these opens lift uniquely to
opens of the original source. Each reduced component maps universally
homeomorphically to Spec A' by hD. The lifted component does also: the reduction
immersion is surjective. Integrality descends across this source thickening with
identity thickening on T. Surjectivity follows from that of the composite with
reduction. After any base change, reduction is still surjective: lift two points
with the same image to the reduced component and use its injectivity to identify
them. This proves universal injectivity. Transport through the affine identifications. -/
theorem finite_scheme_components_of_split_tensor_algebra
    (S : Scheme.{u}) [IsAffine S] {Z : Scheme.{u}} [IsAffine Z] (g : Z ⟶ S)
    (c : Γ(S, ⊤)) (A' : Type u) [CommRing A']
    [Algebra (Localization.Away c) A'] [Algebra Γ(S, ⊤) A']
    [IsScalarTower Γ(S, ⊤) (Localization.Away c) A']
    [Module.Finite (Localization.Away c) A']
    [Algebra.Etale (Localization.Away c) A']
    (hSurj : Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))))
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra A' (D j)]
    (hD : ∀ j, IsUniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))))
    (he : letI := g.appTop.hom.toAlgebra
      letI := Algebra.TensorProduct.rightAlgebra (R := Γ(S, ⊤)) (A := Γ(Z, ⊤)) (B := A')
      Nonempty (((Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A') ⧸ _root_.nilradical (Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A'))
        ≃ₐ[A'] (∀ j, D j))) :
    ∃ (T : Scheme.{u}) (p : T ⟶ (S.basicOpen c).toScheme),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ (W : Fin r → (pullback g (p ≫ (S.basicOpen c).ι)).Opens),
        (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
        ∀ i, IsUniversalHomeomorphism
          ((W i).ι ≫ pullback.snd g (p ≫ (S.basicOpen c).ι)) := by
  set_option backward.isDefEq.respectTransparency false in
   set_option backward.isDefEq.respectTransparency.types false in
    classical
    let eU : (S.basicOpen c).toScheme ≅ Spec (.of (Localization.Away c)) :=
      S.isoOfEq (S.map_PrimeSpectrum_basicOpen_of_affine c).symm ≪≫
        S.isoSpec.hom.preimageIso (PrimeSpectrum.basicOpen c) ≪≫ basicOpenIsoSpecAway c
    let a : Spec (.of A') ⟶ Spec (.of (Localization.Away c)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))
    let p := a ≫ eU.inv
    have haFinite : IsFinite a := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    have haEtale : Etale a := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.mpr inferInstance
    have hpFinite : IsFinite p := inferInstance
    have hpEtale : Etale p := inferInstance
    have haSurj : Surjective a := hSurj
    have hpSurj : Surjective p := inferInstance
    refine ⟨Spec (.of A'), p, hpFinite, hpEtale, hpSurj, ?_⟩
    let := g.appTop.hom.toAlgebra
    let := Algebra.TensorProduct.rightAlgebra
      (R := Γ(S, ⊤)) (A := Γ(Z, ⊤)) (B := A')
    have hpcomp : p ≫ (S.basicOpen c).ι =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) A')) ≫ S.isoSpec.inv := by
      apply (cancel_mono S.isoSpec.hom).mp
      dsimp [p, a, eU]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Scheme.isoOfEq_inv_ι_assoc, Scheme.Hom.preimageIso_inv_ι]
      rw [← basicOpenIsoSpecAway_hom_SpecMap, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq
        Γ(S, ⊤) (Localization.Away c) A').symm
    let b : Spec (.of A') ⟶ Spec Γ(S, ⊤) :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) A'))
    let q := pullback.map g (p ≫ (S.basicOpen c).ι)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(Z, ⊤)))) b
      Z.isoSpec.hom (𝟙 _) S.isoSpec.hom
      (Z.isoSpec_hom_naturality g).symm (by simp [b, hpcomp])
    let eP := asIso q ≪≫ pullbackSpecIso Γ(S, ⊤) Γ(Z, ⊤) A'
    have heP : eP.hom ≫ Spec.map
        (CommRingCat.ofHom (algebraMap A' (Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A'))) =
        pullback.snd g (p ≫ (S.basicOpen c).ι) := by
      change q ≫ (pullbackSpecIso Γ(S, ⊤) Γ(Z, ⊤) A').hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight
          (R := Γ(S, ⊤)) (A := Γ(Z, ⊤)) (B := A')))) = _
      rw [pullbackSpecIso_hom_snd Γ(S, ⊤) Γ(Z, ⊤) A']
      simp [q, b, pullback.map]
    obtain ⟨V, hcover, hdisj, hV⟩ := spectrum_components_of_split_reduction
      A' (Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A') r D hD he
    refine ⟨fun i ↦ eP.hom ⁻¹ᵁ V i, ?_, ?_, ?_⟩
    · rw [← Scheme.Hom.preimage_iSup, hcover]
      exact Scheme.Hom.preimage_top _
    · intro i j hij
      rw [disjoint_iff] at ⊢
      rw [← Scheme.Hom.preimage_inf, (hdisj hij).eq_bot]
      exact Scheme.Hom.preimage_bot _
    · intro i
      have hVi := hV i
      have hh : IsUniversalHomeomorphism
          ((eP.hom.preimageIso (V i)).hom ≫ (V i).ι ≫
            Spec.map (CommRingCat.ofHom (algebraMap A' (Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A')))) :=
        inferInstance
      simpa only [Scheme.Hom.preimageIso_hom_ι_assoc, Category.assoc, heP] using hh

end AlgebraicGeometry.Scheme
