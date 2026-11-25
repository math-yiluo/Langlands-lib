/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Sectionwise fraction-kernel comparison

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks Project, Constructions, Tags 01OA and 01O4, affine fraction-chart calculation and
  localization by a degree-one generator
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry
open Scheme.Modules
open scoped TensorProduct

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection
  SymmetricAlgebraSheaf.gradedAlgebraData Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι
  pulledQuotient pulledTautologicalGenerator quotientGeneratorCoefficient
  quotientSymmetricGenerator degreeOneQuotientFraction quotientFractionSource

private theorem coefficient_smul {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient h E L q U W hWU l m • l =
      q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)) := by
  unfold quotientGeneratorCoefficient
  exact Function.invFun_eq (hl.bijective.surjective _)

private theorem coefficient_restrict {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W V : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hVW : V.1 ≤ W.1) (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
    (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient h E L q U V (hVW.trans hWU)
        (L.val.map (homOfLE hVW).op l) m =
      T.presheaf.map (homOfLE hVW).op
        (quotientGeneratorCoefficient h E L q U W hWU l m) := by
  apply (hl.map hVW).smul_left_injective
  dsimp only
  erw [coefficient_smul h E L q U V (hVW.trans hWU) _ (hl.map hVW),
    ← map_smul L (homOfLE hVW), coefficient_smul h E L q U W hWU l hl,
    ← Hom.app_presheaf_map, presheaf_map_map_apply]
  rfl

private theorem affine_factorization {T : Scheme.{u}} (W : T.affineOpens)
    (C : CommRingCat.{u}) (k : W.1.toScheme ⟶ Spec C) :
    W.2.isoSpec.inv ≫ k = Spec.map
      ((Scheme.ΓSpecIso C).inv ≫ k.appTop ≫ W.1.topIso.hom) := by
  rw [IsAffineOpen.isoSpec_inv, Category.assoc, ← Scheme.isoSpec_inv_naturality,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  rfl

private theorem affine_kernel_of_coefficients {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (M L : T.Modules)
    (p : (tensorPullback h).obj E ⟶ M) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (e : Γ(M, W.1)) (he : IsFreeGenerator e)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (b : Γ(T, W.1)) (hb : IsUnit b)
    (hgen : ∀ v : Γ(E, U.1),
      b * he.coeff (p.app W.1 (((tensorPullback h).obj E).val.map
        (homOfLE hWU).op (tensorPullbackSection h E U.1 v))) =
      hl.coeff (q.app W.1 (((tensorPullback h).obj E).val.map
        (homOfLE hWU).op (tensorPullbackSection h E U.1 v)))) :
    ∀ x : Γ((tensorPullback h).obj E, W.1), p.app W.1 x = 0 ↔ q.app W.1 x = 0 := by
  classical
  let : Algebra Γ(S, U.1) Γ(T, W.1) := (h.appLE U.1 W.1 hWU).hom.toAlgebra
  let : ∀ G : S.Modules, Module Γ(S, U.1) Γ((tensorPullback h).obj G, W.1) :=
    fun G ↦ Module.compHom _ (h.appLE U.1 W.1 hWU).hom
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections h U W hWU
  have hcoeff (t : Γ(E, U.1) ⊗[Γ(S, U.1)] Γ(T, W.1)) :
      b * he.coeff (p.app W.1 (c E inferInstance t)) =
        hl.coeff (q.app W.1 (c E inferInstance t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul v r =>
      rw [hp]
      have hs : (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app E).val.app
          (op U.1) v) = tensorPullbackSection h E U.1 v := by
        unfold tensorPullbackSection
        exact Classical.choose_spec (exists_tensorPullbackAdjunction h) E (op U.1) v
      rw [hs, Hom.app_smul, Hom.app_smul, he.coeff_smul_left, hl.coeff_smul_left,
        ← mul_assoc, mul_comm b r, mul_assoc]
      exact congrArg (r * ·) (hgen v)
    | add t t' ht ht' =>
      simp only [map_add, he.coeff_add, hl.coeff_add, mul_add, ht, ht']
  intro x
  obtain ⟨t, rfl⟩ := (hc E inferInstance).surjective x
  have hz (y : Γ(M, W.1)) : he.coeff y = 0 ↔ y = 0 := by
    rw [he.coeff_eq_iff, zero_smul, eq_comm]
  have hz' (y : Γ(L, W.1)) : hl.coeff y = 0 ↔ y = 0 := by
    rw [hl.coeff_eq_iff, zero_smul, eq_comm]
  rw [← hz, ← hz', ← hcoeff]
  exact (hb.mul_right_inj).symm.trans (by rw [mul_zero])

@[irreducible] private noncomputable def unitLocalizationInverse {R : Type u}
    [CommRing R] (b : R) (hb : IsUnit b) : Localization.Away b →+* R :=
  (IsLocalization.atUnit R (Localization.Away b) b hb).symm.toRingHom

private theorem unitLocalizationInverse_algebraMap {R : Type u} [CommRing R]
    (b : R) (hb : IsUnit b) (r : R) :
    unitLocalizationInverse b hb (algebraMap R (Localization.Away b) r) = r := by
  unfold unitLocalizationInverse
  exact (IsLocalization.atUnit R (Localization.Away b) b hb).symm_apply_apply r

private theorem unitLocalizationInverse_fraction {R : Type u} [CommRing R]
    (b : R) (hb : IsUnit b) (r : R) :
    unitLocalizationInverse b hb
        (Localization.mk r (⟨b, ⟨1, pow_one b⟩⟩ : Submonoid.powers b)) * b = r := by
  have H : Localization.mk r (⟨b, ⟨1, pow_one b⟩⟩ : Submonoid.powers b) *
      algebraMap R (Localization.Away b) b = algebraMap R (Localization.Away b) r := by
    simpa only [Localization.mk_eq_mk'] using
      (IsLocalization.mk'_spec (Localization.Away b) r
        (⟨b, ⟨1, pow_one b⟩⟩ : Submonoid.powers b))
  have H' := congrArg (unitLocalizationInverse b hb) H
  simpa only [map_mul, unitLocalizationInverse_algebraMap] using H'

private theorem affine_ringMap {T : Scheme.{u}} (W : T.affineOpens)
    (C : CommRingCat.{u}) (φ : C ⟶ Γ(T, W.1)) :
    (Scheme.ΓSpecIso C).inv ≫ (W.2.isoSpec.hom ≫ Spec.map φ).appTop ≫
      W.1.topIso.hom = φ := by
  apply Spec.map_injective
  rw [← affine_factorization]
  simp only [Iso.inv_hom_id_assoc]

private theorem unitFractionSource_section {T : Scheme.{u}} (W : T.affineOpens)
    (b : Γ(T, W.1)) (hb : IsUnit b) :
    W.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (unitLocalizationInverse b hb)) ≫
      quotientFractionSource W b = W.1.ι := by
  have hs : CommRingCat.ofHom (algebraMap Γ(T, W.1) (Localization.Away b)) ≫
      CommRingCat.ofHom (unitLocalizationInverse b hb) = 𝟙 _ := by
    ext z
    exact unitLocalizationInverse_algebraMap b hb z
  simp only [quotientFractionSource]
  rw [← Spec.map_comp_assoc, hs, Spec.map_id]
  erw [Category.id_comp, Iso.hom_inv_id_assoc]

private theorem unitFraction_chart_factor {T P : Scheme.{u}} (W : T.affineOpens)
    (b : Γ(T, W.1)) (hb : IsUnit b) (F : T ⟶ P) (C : CommRingCat.{u})
    (ρ : C ⟶ CommRingCat.of (Localization.Away b)) (j : Spec C ⟶ P)
    (hρ : quotientFractionSource W b ≫ F = Spec.map ρ ≫ j) :
    W.1.ι ≫ F = (W.2.isoSpec.hom ≫
      Spec.map (ρ ≫ CommRingCat.ofHom (unitLocalizationInverse b hb))) ≫ j := by
  rw [← unitFractionSource_section W b hb, Category.assoc, Category.assoc, hρ,
    Spec.map_comp]
  simp only [Category.assoc]

private theorem affine_kernel_of_fraction_values {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (M L : T.Modules)
    (p : (tensorPullback h).obj E ⟶ M) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (e : Γ(M, W.1)) (he : IsFreeGenerator e)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (b : Γ(T, W.1)) (hb : IsUnit b)
    (C : CommRingCat.{u}) (ρ : C →+* Localization.Away b) (κ : C →+* Γ(T, W.1))
    (hκ : κ = (unitLocalizationInverse b hb).comp ρ)
    (z : Γ(E, U.1) → C) (c d : Γ(E, U.1) → Γ(T, W.1))
    (hp : ∀ v : Γ(E, U.1),
      p.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 v)) = κ (z v) • e)
    (hq : ∀ v : Γ(E, U.1), d v • l =
      q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 v)))
    (hρ : ∀ v : Γ(E, U.1), ρ (z v) = Localization.mk (c v)
      (⟨b ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers b)) (hcd : ∀ v, c v = d v) :
    ∀ x : Γ((tensorPullback h).obj E, W.1), p.app W.1 x = 0 ↔ q.app W.1 x = 0 := by
  apply affine_kernel_of_coefficients h E M L p q U W hWU e he l hl b hb
  intro v
  rw [hp v, he.coeff_smul_self, ← hq v, hl.coeff_smul_self, hκ]
  have hh : ρ (z v) = Localization.mk (d v)
      (⟨b, ⟨1, pow_one b⟩⟩ : Submonoid.powers b) := by
    simpa only [pow_one, hcd v] using hρ v
  change b * unitLocalizationInverse b hb (ρ (z v)) = d v
  rw [hh, mul_comm]
  exact unitLocalizationInverse_fraction b hb (d v)

private theorem unit_chart_kernel {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hc : ψ.HasQuotientFractionCharts h E L q F)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1))
    (hm : IsUnit (quotientGeneratorCoefficient h E L q U W hWU l m)) :
    ∀ x : Γ((tensorPullback h).obj E, W.1),
      (pulledQuotient D h F hc.1).app W.1 x = 0 ↔ q.app W.1 x = 0 := by
  let b := quotientGeneratorCoefficient h E L q U W hWU l m
  let σ := unitLocalizationInverse b hm
  obtain ⟨ρ, hρ⟩ := (hc.2 U W hWU l hl).2.2.2.1 m
  let κ := σ.comp ρ
  let k := W.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom κ)
  have hk : W.1.ι ≫ F = k ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U :=
    unitFraction_chart_factor W b hm F _ (CommRingCat.ofHom ρ) _ hρ.2.2.1
  have hWF : W.1 ≤ F ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1) := by
    simpa only [← Scheme.Hom.comp_preimage, hc.1] using hWU
  obtain ⟨he, _, hp⟩ :=
    lineQuotient_pulled_chart_normalization h E D F hc.1 U W hWU hWF m k hk
  have hκ : ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom).hom = κ :=
    congrArg CommRingCat.Hom.hom (affine_ringMap W _ (CommRingCat.ofHom κ))
  exact affine_kernel_of_fraction_values h E _ L (pulledQuotient D h F hc.1) q
    U W hWU _ he l hl b hm
    (.of (HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val))
    ρ ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom).hom hκ
    (fun v ↦ degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
      (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U v))
    (fun v ↦ ψ.quotientCoefficient U W hWU l 1 (quotientSymmetricGenerator E U v))
    (quotientGeneratorCoefficient h E L q U W hWU l)
    hp (coefficient_smul h E L q U W hWU l hl)
    (fun v ↦ hρ.1 1 (quotientSymmetricGenerator E U v))
    (hc.2 U W hWU l hl).2.1

private theorem kernel_eq_of_locally {T : Scheme.{u}} (A M L : T.Modules)
    (p : A ⟶ M) (q : A ⟶ L)
    (hlocal : ∀ (O : T.Opens) (t : T), t ∈ O →
      ∃ (V : T.affineOpens) (_ : t ∈ V.1) (_ : V.1 ≤ O),
        ∀ z : Γ(A, V.1), p.app V.1 z = 0 ↔ q.app V.1 z = 0) :
    ∀ (U : T.Opens) (x : Γ(A, U)), p.app U x = 0 ↔ q.app U x = 0 := by
  intro U x
  constructor
  · intro hp
    apply TopCat.Presheaf.IsSheaf.section_ext L.isSheaf
    intro t ht
    obtain ⟨V, htV, hVU, hk⟩ := hlocal U t ht
    refine ⟨V.1, hVU, htV, ?_⟩
    rw [map_zero, ← Hom.app_presheaf_map]
    apply (hk _).mp
    rw [Hom.app_presheaf_map, hp, map_zero]
  · intro hq
    apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
    intro t ht
    obtain ⟨V, htV, hVU, hk⟩ := hlocal U t ht
    refine ⟨V.1, hVU, htV, ?_⟩
    rw [map_zero, ← Hom.app_presheaf_map]
    apply (hk _).mpr
    rw [Hom.app_presheaf_map, hq, map_zero]

private theorem kernel_eq_of_unit_charts {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (M L : T.Modules) [L.IsInvertible]
    (p : (tensorPullback h).obj E ⟶ M) (q : (tensorPullback h).obj E ⟶ L)
    (hcover : ∀ (U : S.affineOpens) (W : T.affineOpens)
      (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)), IsFreeGenerator l →
        (⨆ m : Γ(E, U.1),
          T.basicOpen (quotientGeneratorCoefficient h E L q U W hWU l m)) = W.1)
    (hchart : ∀ (U : S.affineOpens) (W : T.affineOpens)
      (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)), IsFreeGenerator l →
      ∀ m : Γ(E, U.1), IsUnit (quotientGeneratorCoefficient h E L q U W hWU l m) →
        ∀ z : Γ((tensorPullback h).obj E, W.1),
          p.app W.1 z = 0 ↔ q.app W.1 z = 0) :
    ∀ (U : T.Opens) (x : Γ((tensorPullback h).obj E, U)),
      p.app U x = 0 ↔ q.app U x = 0 := by
  apply kernel_eq_of_locally _ M L p q
  intro O t ht
  obtain ⟨B, hB, htB, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h t) (U := ⊤) trivial
  let A : S.affineOpens := ⟨B, hB⟩
  have htA : t ∈ O ⊓ h ⁻¹ᵁ A.1 := ⟨ht, htB⟩
  let : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨W, htW, hWA, l, hl⟩ := exists_isFreeGenerator L htA
  have hWO : W.1 ≤ O := hWA.trans inf_le_left
  have hWU : W.1 ≤ h ⁻¹ᵁ A.1 := hWA.trans inf_le_right
  have htcover : t ∈ ⨆ m : Γ(E, A.1),
      T.basicOpen (quotientGeneratorCoefficient h E L q A W hWU l m) := by
    rw [hcover A W hWU l hl]
    exact htW
  obtain ⟨m, htm⟩ := TopologicalSpace.Opens.mem_iSup.mp htcover
  let b := quotientGeneratorCoefficient h E L q A W hWU l m
  let V : T.affineOpens := ⟨T.basicOpen b, W.2.basicOpen b⟩
  have hVW : V.1 ≤ W.1 := T.basicOpen_le b
  have hunit : IsUnit (quotientGeneratorCoefficient h E L q A V
      (hVW.trans hWU) (L.val.map (homOfLE hVW).op l) m) := by
    rw [coefficient_restrict h E L q A W V hWU hVW l hl m]
    exact T.toRingedSpace.isUnit_res_basicOpen b
  exact ⟨V, htm, hVW.trans hWO,
    hchart A V (hVW.trans hWU) _ (hl.map hVW) m hunit⟩

/-- The fraction-chart calculation identifies the two quotient maps on every section. -/
theorem lineQuotient_fraction_kernel_sections {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hcharts : ψ.HasQuotientFractionCharts h E L q F) :
    ∀ (U : T.Opens) (x : Γ((tensorPullback h).obj E, U)),
      (pulledQuotient D h F hcharts.1).app U x = 0 ↔ q.app U x = 0 := by
  have _ := hψ
  exact kernel_eq_of_unit_charts h E _ L (pulledQuotient D h F hcharts.1) q
    (fun U W hWU l hl ↦ (hcharts.2 U W hWU l hl).2.2.1)
    (fun U W hWU l hl m hm ↦ unit_chart_kernel h E D L q ψ F hcharts
      U W hWU l hl m hm)

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
