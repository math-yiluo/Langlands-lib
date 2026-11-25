/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra

/-!
# The extended Rees algebra as a blow-up chart

Let `R` be a ring, `I ⊆ R` an ideal and `J = I R[t] + (t) ⊆ R[t]` the ideal of
`V(I) × {0} ⊆ Spec R × 𝔸¹`. The chart of the blow-up `Bl_J (Spec R[t])` at the degree-one
element `t·X` of the Rees algebra of `J` is the spectrum of the extended Rees algebra
`R[t, I t⁻¹] ⊆ R[t, t⁻¹]`: its coordinate ring is `R[t][J/t]`, generated over `R[t]` by `t / t`
and the fractions `x / t`, `x ∈ I`.

This is the affine-local comparison between the two descriptions of the deformation to the
normal cone (blueprint `definition-deformation-normal-bundle`): the Rees model
`Spec R[t, I t⁻¹]` used by `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`, and the
blow-up model `Bl_{V(I) × 0}(Spec R × 𝔸¹)`.

## Main definitions

- `AlgebraicGeometry.AffineBlowup.deformationCenter I`: the ideal `J = I R[t] + (t)`.
- `AlgebraicGeometry.AffineBlowup.chartEquivExtendedReesAlgebra I`: the ring isomorphism
  `Away (reesGrading J) (t·X) ≃+* R[t, I t⁻¹]`, compatible with the maps from `R[t]`.
- `AlgebraicGeometry.AffineBlowup.deformationChart I`: the open immersion
  `Spec R[t, I t⁻¹] ⟶ Bl_J (Spec R[t])` onto the basic open `D₊(t·X)`, over `Spec R[t]`.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial LaurentPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The ideal `J = I R[t] + (t) ⊆ R[t]` of `V(I) × {0}` in `Spec R × 𝔸¹`. -/
noncomputable def deformationCenter : Ideal R[X] :=
  I.map Polynomial.C ⊔ Ideal.span {X}

variable {I}

lemma X_mem_deformationCenter : (X : R[X]) ∈ deformationCenter I :=
  Ideal.mem_sup_right (Ideal.subset_span rfl)

lemma C_mem_deformationCenter {x : R} (hx : x ∈ I) :
    Polynomial.C x ∈ deformationCenter I :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

lemma coeff_zero_mem_of_mem_deformationCenter {p : R[X]} (hp : p ∈ deformationCenter I) :
    p.coeff 0 ∈ I := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hp
  rw [coeff_add]
  refine I.add_mem (Ideal.mem_map_C_iff.mp hy 0) ?_
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  simp

lemma mem_deformationCenter_iff {p : R[X]} : p ∈ deformationCenter I ↔ p.coeff 0 ∈ I := by
  refine ⟨coeff_zero_mem_of_mem_deformationCenter, fun h ↦ ?_⟩
  rw [← X_mul_divX_add p]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ X_mem_deformationCenter)
    (C_mem_deformationCenter h)

variable (R) in
/-- `R[t]_t = R[t, t⁻¹]` as `R[t]`-algebras. -/
noncomputable def awayXEquivLaurent : Localization.Away (X : R[X]) ≃ₐ[R[X]] R[T;T⁻¹] :=
  IsLocalization.algEquiv (Submonoid.powers (X : R[X])) _ _

lemma awayXEquivLaurent_chartFraction (n : ℕ) (x : R[X]) :
    awayXEquivLaurent R (chartFraction X n x) = toLaurent x * T (-n) := by
  rw [chartFraction, Localization.mk_eq_mk', awayXEquivLaurent, IsLocalization.algEquiv_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * algebraMap R[X] R[T;T⁻¹] (X ^ n)
  rw [algebraMap_X_pow, algebraMap_eq_toLaurent, mul_T_assoc, neg_add_cancel, T_zero, mul_one]

lemma awayXEquivLaurent_algebraMap (p : R[X]) :
    awayXEquivLaurent R (algebraMap R[X] _ p) = toLaurent p := by
  rw [AlgEquiv.commutes, algebraMap_eq_toLaurent]

lemma toLaurent_mul_T_neg_one_mem {x : R[X]} (hx : x ∈ deformationCenter I) :
    toLaurent x * T (-1) ∈ I.extendedReesAlgebra := by
  have h : toLaurent x * T (-1) =
      toLaurent (divX x) + LaurentPolynomial.C (x.coeff 0) * T (-1) := by
    conv_lhs => rw [← X_mul_divX_add x]
    rw [map_add, map_mul, toLaurent_X, toLaurent_C, add_mul, mul_comm (T 1), mul_T_assoc]
    simp
  rw [h]
  exact Subalgebra.add_mem _ (Ideal.toLaurent_mem_extendedReesAlgebra _)
    (Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra
      (coeff_zero_mem_of_mem_deformationCenter hx))

lemma awayXEquivLaurent_mem_extendedReesAlgebra {z : Localization.Away (X : R[X])}
    (hz : z ∈ chartRing (deformationCenter I) X) :
    awayXEquivLaurent R z ∈ I.extendedReesAlgebra := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hz
    rw [awayXEquivLaurent_chartFraction]
    simpa using toLaurent_mul_T_neg_one_mem hx
  | algebraMap p =>
    rw [awayXEquivLaurent_algebraMap]
    exact Ideal.toLaurent_mem_extendedReesAlgebra p
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

lemma exists_mem_chartRing_of_mem_extendedReesAlgebra {f : R[T;T⁻¹]}
    (hf : f ∈ I.extendedReesAlgebra) :
    ∃ z ∈ chartRing (deformationCenter I) X, awayXEquivLaurent R z = f := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain rfl | ⟨x, hx, rfl⟩ := hf
    · exact ⟨algebraMap R[X] _ X, Subalgebra.algebraMap_mem _ _,
        by rw [awayXEquivLaurent_algebraMap, toLaurent_X]⟩
    · have hx1 : Polynomial.C x ∈ deformationCenter I ^ 1 := by
        rw [pow_one]; exact C_mem_deformationCenter hx
      exact ⟨_, chartFraction_mem_chartRing _ hx1,
        by rw [awayXEquivLaurent_chartFraction, toLaurent_C]; simp⟩
  | algebraMap r =>
    exact ⟨algebraMap R[X] _ (Polynomial.C r), Subalgebra.algebraMap_mem _ _,
      by rw [awayXEquivLaurent_algebraMap, toLaurent_C, LaurentPolynomial.C_eq_algebraMap]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨z + w, Subalgebra.add_mem _ hz hw, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨z * w, Subalgebra.mul_mem _ hz hw, map_mul _ _ _⟩

variable (I)

/-- The map `Away (reesGrading J) (t·X) →+* R[t, t⁻¹]`, `x·Xⁿ / (t·X)ⁿ ↦ x t⁻ⁿ`. -/
noncomputable def chartToLaurent :
    HomogeneousLocalization.Away (reesGrading (deformationCenter I))
      (reesX _ X X_mem_deformationCenter) →+* R[T;T⁻¹] :=
  (awayXEquivLaurent R).toRingEquiv.toRingHom.comp
    ((chartRing (deformationCenter I) X).val.toRingHom.comp
      (homogeneousAwayToChart _ X_mem_deformationCenter))

lemma chartToLaurent_apply (z) : chartToLaurent I z =
    awayXEquivLaurent R (homogeneousAwayToChart _ X_mem_deformationCenter z :
      Localization.Away (X : R[X])) := rfl

lemma chartToLaurent_mem (z) : chartToLaurent I z ∈ I.extendedReesAlgebra :=
  awayXEquivLaurent_mem_extendedReesAlgebra (homogeneousAwayToChart _ _ z).2

/-- **The blow-up chart at `t·X` is the extended Rees algebra**: for `J = I R[t] + (t)`,
`Away (reesGrading J) (t·X) ≃+* R[t, I t⁻¹]`, `x·Xⁿ / (t·X)ⁿ ↦ x t⁻ⁿ`.
(Blueprint `definition-deformation-normal-bundle`, affine-local comparison of the Rees model with
the blow-up model.) -/
noncomputable def chartEquivExtendedReesAlgebra :
    HomogeneousLocalization.Away (reesGrading (deformationCenter I))
      (reesX _ X X_mem_deformationCenter) ≃+* I.extendedReesAlgebra :=
  RingEquiv.ofBijective ((chartToLaurent I).codRestrict I.extendedReesAlgebra
    (chartToLaurent_mem I)) <| by
    constructor
    · intro z w h
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, chartToLaurent_apply] at h'
      exact homogeneousAwayToChart_injective _ _ (Subtype.ext ((awayXEquivLaurent R).injective h'))
    · rintro ⟨f, hf⟩
      obtain ⟨z, hz, rfl⟩ := exists_mem_chartRing_of_mem_extendedReesAlgebra hf
      obtain ⟨w, hw⟩ := homogeneousAwayToChart_surjective _ X_mem_deformationCenter ⟨z, hz⟩
      exact ⟨w, Subtype.ext (by simp [chartToLaurent_apply, hw])⟩

lemma coe_chartEquivExtendedReesAlgebra (z) :
    (chartEquivExtendedReesAlgebra I z : R[T;T⁻¹]) = chartToLaurent I z := rfl

/-- The comparison isomorphism is compatible with the maps from `R[t]`. -/
lemma chartEquivExtendedReesAlgebra_awayAlgebraMap (p : R[X]) :
    chartEquivExtendedReesAlgebra I (awayAlgebraMap _ _ p) = I.toExtendedReesAlgebra p := by
  apply Subtype.ext
  rw [coe_chartEquivExtendedReesAlgebra, chartToLaurent_apply,
    homogeneousAwayToChart_awayAlgebraMap, Ideal.coe_toExtendedReesAlgebra]
  exact awayXEquivLaurent_algebraMap p

lemma chartEquivExtendedReesAlgebra_comp_awayAlgebraMap :
    (chartEquivExtendedReesAlgebra I).toRingHom.comp
      (awayAlgebraMap _ (reesX _ X X_mem_deformationCenter)) = I.toExtendedReesAlgebra :=
  RingHom.ext (chartEquivExtendedReesAlgebra_awayAlgebraMap I)

/-! ### The chart as an open subscheme of the blow-up -/

/-- **The Rees model of the deformation space is the chart `D₊(t·X)` of the blow-up**: the open
immersion `Spec R[t, I t⁻¹] ⟶ Bl_J (Spec R[t])`, `J = I R[t] + (t)`, onto the basic open of
`t·X`. (Blueprint `definition-deformation-normal-bundle`, affine-local form.) -/
noncomputable def deformationChart :
    Spec (.of I.extendedReesAlgebra) ⟶ AffineBlowup (deformationCenter I) :=
  Spec.map (CommRingCat.ofHom (chartEquivExtendedReesAlgebra I).toRingHom) ≫
    chart _ _ (reesX_mem _ X X_mem_deformationCenter)

instance : IsIso (Spec.map (CommRingCat.ofHom (chartEquivExtendedReesAlgebra I).toRingHom)) :=
  inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso
    (chartEquivExtendedReesAlgebra I)).hom))

instance : IsOpenImmersion (deformationChart I) := by
  unfold deformationChart; infer_instance

lemma opensRange_deformationChart :
    (deformationChart I).opensRange =
      Proj.basicOpen (reesGrading (deformationCenter I)) (reesX _ X X_mem_deformationCenter) := by
  unfold deformationChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_chart]

/-- The chart lies over `Spec R[t]` via `R[t] ⊆ R[t, I t⁻¹]`. -/
@[reassoc]
lemma deformationChart_toSpec :
    deformationChart I ≫ toSpec _ = Spec.map (CommRingCat.ofHom I.toExtendedReesAlgebra) := by
  rw [deformationChart, Category.assoc, chart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartEquivExtendedReesAlgebra_comp_awayAlgebraMap]

end AlgebraicGeometry.AffineBlowup
