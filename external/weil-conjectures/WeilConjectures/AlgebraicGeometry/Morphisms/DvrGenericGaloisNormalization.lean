/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-! # Finite normal models of generic Galois covers over a DVR

## References

* Stacks Project, Tags 032L, 033C, 035L and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Smooth ascent on affine charts, followed by localization at the source point.
private theorem normal_stalks_of_smooth_integral_base {Y Z : Scheme.{u}} [IsIntegral Z]
    (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (g : Y ⟶ Z) [Smooth g] (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨U, hU, V, hV, hy, hVU, _⟩ := Smooth.exists_isStandardSmooth g y
  let : Nonempty U := ⟨⟨g y, hVU hy⟩⟩
  let : IsIntegrallyClosed Γ(Z, U) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hZ U
  have hnormal := (g.smooth_appLE hU hV hVU).isNormalRing (fun q hq ↦ by
    let : IsIntegrallyClosed (Localization.AtPrime q) :=
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
    exact ⟨inferInstance, inferInstance⟩)
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  let q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  obtain ⟨hd, hi⟩ := hnormal q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (Y.presheaf.stalk y)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem fractionRing_isLocalizationAway
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) :
    IsLocalization.Away pi (FractionRing B) := by
  let : IsFractionRing B (Localization.Away pi) :=
    IsLocalization.of_le_of_exists_dvd (Submonoid.powers pi) (nonZeroDivisors B)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hpi.ne_zero) (by
        intro b hb
        obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
          (nonZeroDivisors.ne_zero hb) hpi
        exact ⟨pi ^ n, ⟨n, rfl⟩, ⟨↑v⁻¹, by
          calc pi ^ n = (↑v * ↑v⁻¹) * pi ^ n := by simp
               _ = ↑v * pi ^ n * ↑v⁻¹ := by ring⟩⟩)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers pi)
    (IsLocalization.algEquiv (nonZeroDivisors B) (Localization.Away pi) (FractionRing B))

set_option backward.isDefEq.respectTransparency false in
private theorem finite_normalization_of_normal_open
    {N : Scheme.{u}} [IsNoetherian N] [IsIntegral N]
    (hn : ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z))
    (V : N.Opens) {X : Scheme.{u}} (p : X ⟶ V.toScheme) [IsFinite p] [Etale p]
    (f : X ⟶ N) [QuasiCompact f] [QuasiSeparated f] (hf : f = p ≫ V.ι) :
    IsFinite f.fromNormalization := by
  subst f
  let Q : V.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ p inferInstance, (show IsFinite p from inferInstance)⟩
  let a := p ≫ V.ι
  refine { finite_app := ?_ }
  intro B hB
  let : Algebra Γ(N, B) Γ(X, a ⁻¹ᵁ B) := (a.app B).hom.toAlgebra
  have hfin : Module.Finite Γ(N, B) (integralClosure Γ(N, B) Γ(X, a ⁻¹ᵁ B)) :=
    finiteEtale_open_integralClosure_finite hn V Q B hB
  rw [Scheme.Hom.fromNormalization_app a hB]
  exact (RingHom.finite_respectsIso.cancel_right_isIso
    (CommRingCat.ofHom (algebraMap _ _))
    (Scheme.Hom.normalizationObjIso a hB).inv).2 (RingHom.finite_algebraMap.2 hfin)

set_option backward.isDefEq.respectTransparency false in
/-- A finite Galois generic cover pulled back to a DVR has finite relative normalization
and normal local rings. -/
theorem dvr_generic_galois_normalization
    (B A : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    [IsDomain A] [IsDiscreteValuationRing A]
    (q : Spec A ⟶ Spec B)
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    IsFinite a.fromNormalization ∧
      ∀ x : a.normalization, IsDomain (a.normalization.presheaf.stalk x) ∧
        IsIntegrallyClosed (a.normalization.presheaf.stalk x) := by
  classical
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  let K := FractionRing B
  let j := Spec.map (CommRingCat.ofHom (algebraMap B K))
  let a := pullback.snd (p ≫ j) q
  let (i : Fin r) : FiniteDimensional K (E i) := (hE i).1
  let (i : Fin r) : IsGalois K (E i) := (hE i).2
  let (i : Fin r) : Algebra.FormallyEtale K (E i) :=
    Algebra.FormallyEtale.of_isSeparable K (E i)
  let (i : Fin r) : Algebra.Etale K (E i) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let f (i : Fin r) := Spec.map (CommRingCat.ofHom (algebraMap K (E i)))
  have hf : ∀ i, Etale (f i) := by
    intro i
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  -- Mathlib's finite-product comparison uses an index in the ring universe.
  let R (i : ULift.{u} (Fin r)) := CommRingCat.of (E i.down)
  let f' (i : ULift.{u} (Fin r)) := f i.down
  have hdesc : Sigma.desc f' = sigmaSpec R ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (∀ i : ULift.{u} (Fin r), E i.down))) := by
    ext i
    rw [Sigma.ι_comp_desc, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
    rfl
  let : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap K (∀ i : ULift.{u} (Fin r), E i.down)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite (Sigma.desc f') := by rw [hdesc]; infer_instance
  let er := Sigma.reindex (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
    (fun i ↦ Spec (CommRingCat.of (E i)))
  have her : er.hom ≫ Sigma.desc f = Sigma.desc f' := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_reindex_hom, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    rfl
  have : IsFinite (Sigma.desc f) := by
    have h : Sigma.desc f = er.inv ≫ Sigma.desc f' := (er.eq_inv_comp).mpr her
    rw [h]
    exact MorphismProperty.comp_mem _ er.inv (Sigma.desc f')
      (MorphismProperty.of_isIso _ er.inv) ‹IsFinite (Sigma.desc f')›
  have : Etale (Sigma.desc f) := IsZariskiLocalAtSource.sigmaDesc hf
  have : IsFinite p := by rw [← he]; infer_instance
  have : Etale p := by rw [← he]; infer_instance
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  let : IsLocalization.Away pi K := fractionRing_isLocalizationAway B pi hpi
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization pi
  have : Etale a := inferInstance
  have : IsLocallyNoetherian (pullback (p ≫ j) q) :=
    LocallyOfFiniteType.isLocallyNoetherian a
  let N := Spec A
  have hN : ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z) := by
    intro z
    let P := z.asIdeal
    let : IsIntegrallyClosed (Localization.AtPrime P) :=
      isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso A z).commRingCatIsoToRingEquiv.symm
  let g := pullback.snd j q
  let b := (pullbackRightPullbackFstIso j q p).inv ≫
    pullback.snd p (pullback.fst j q)
  have hfactor : a = b ≫ g := by
    simp [a, b, g]
  let V := g.opensRange
  let c := b ≫ g.isoOpensRange.hom
  have hc : a = c ≫ V.ι := by simp [c, V, hfactor]
  have hfinite : IsFinite a.fromNormalization :=
    finite_normalization_of_normal_open hN V c a hc
  exact ⟨hfinite, relativeNormalization_normal_stalks a
    (normal_stalks_of_smooth_integral_base hN a)⟩

end AlgebraicGeometry.Scheme
