/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials

/-!
# Basic opens of the standard charts of the projective line

Let `ℙ¹_k = ProjectiveLine (Spec k)` with its standard charts `D₊(xᵢ) ≅ Spec k[t]`. For a
polynomial `g ≠ 0` we consider the basic open `Dᵢ(g) ⊆ D₊(xᵢ)` where `g(t)` does not vanish. These
opens form a basis of the topology of `ℙ¹_k`, their rings of sections are the localizations
`k[t]_g`, and over each of them `Ω¹_{ℙ¹/k}` is free on `dt`.

## Main definitions and results

- `AlgebraicGeometry.ProjectiveLine.chartBasicOpen`: the basic open `Dᵢ(g)`.
- `AlgebraicGeometry.ProjectiveLine.polyToChartBasicOpen`: the ring map `k[t] → Γ(Dᵢ(g))`.
- `AlgebraicGeometry.ProjectiveLine.isLocalization_chartBasicOpen`: `Γ(Dᵢ(g)) = k[t]_g`.
- `AlgebraicGeometry.ProjectiveLine.isBasis_chartBasicOpen`: the `Dᵢ(g)` form a basis.
- `AlgebraicGeometry.ProjectiveLine.isFreeGenerator_sectionsD_polyToChartBasicOpen_X`: `dt` is a
  free generator of `Ω¹_{ℙ¹/k}` over `Dᵢ(g)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Polynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

variable (k : Type u) [Field k]

/-- The basic open `Dᵢ(g)` of the standard chart `D₊(xᵢ) = Spec k[t]` of `ℙ¹_k`, `t = x_{1-i}/xᵢ`,
where the polynomial `g(t)` does not vanish. -/
abbrev chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    (ProjectiveLine (Spec (.of k))).Opens :=
  (ProjectiveLine (Spec (.of k))).basicOpen (polyEquivChart k (ne_other i) g)

lemma chartBasicOpen_le (i : ULift.{u} (Fin 2)) (g : k[X]) :
    chartBasicOpen k i g ≤ chart k {i} :=
  (ProjectiveLine (Spec (.of k))).basicOpen_le _

lemma isAffineOpen_chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    IsAffineOpen (chartBasicOpen k i g) :=
  (isAffineOpen_chart k (Set.singleton_nonempty i)).basicOpen _

/-- The ring map `k[t] → Γ(ℙ¹_k, Dᵢ(g))`. -/
def polyToChartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    k[X] →+* Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g) :=
  ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (chartBasicOpen_le k i g)).op).hom.comp
    (polyEquivChart k (ne_other i)).toRingHom

/-- The constants of `k[t]` go to the structure map `k → Γ(ℙ¹_k, Dᵢ(g))`. -/
lemma polyToChartBasicOpen_C (i : ULift.{u} (Fin 2)) (g : k[X]) (c : k) :
    polyToChartBasicOpen k i g (C c) =
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).specStructureMap _ c := by
  rw [polyToChartBasicOpen, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, polyEquivChart_apply, polyToChart, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, presheaf_map_chartConst]
  rfl

/-- **The sections of `ℙ¹_k` over `Dᵢ(g)` are the localization `k[t]_g`.** -/
theorem isLocalization_chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    letI := (polyToChartBasicOpen k i g).toAlgebra
    IsLocalization.Away g Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g) := by
  have := (isAffineOpen_chart k (Set.singleton_nonempty i)).isLocalization_basicOpen
    (polyEquivChart k (ne_other i) g)
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (polyEquivChart k (ne_other i) g)) Γ(ProjectiveLine (Spec (.of k)),
      chartBasicOpen k i g) (polyEquivChart k (ne_other i)).symm
  rw [Submonoid.map_powers, RingEquiv.symm_apply_apply] at h
  exact h

/-- **The opens `Dᵢ(g)`, `g ≠ 0`, form a basis of the topology of `ℙ¹_k`.** -/
theorem isBasis_chartBasicOpen :
    Opens.IsBasis (Set.range fun a : (Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) ↦
      chartBasicOpen k a.1 a.2.1) := by
  refine Opens.isBasis_iff_nbhd.2 fun {U x} hx ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((iSup_chart k).ge (Set.mem_univ x))
  obtain ⟨f, hfU, hxf⟩ := (isAffineOpen_chart k (Set.singleton_nonempty i)).exists_basicOpen_le
    ⟨x, hx⟩ hi
  obtain ⟨g, rfl⟩ := (polyEquivChart k (ne_other i)).surjective f
  refine ⟨chartBasicOpen k i g, ⟨⟨i, g, fun hg ↦ ?_⟩, rfl⟩, hxf, hfU⟩
  rw [hg, map_zero, Scheme.basicOpen_zero] at hxf
  exact hxf

/-- The generator `omegaGen k i` of `Ω¹_{ℙ¹/k}` over the chart `D₊(xᵢ)` is a free generator. -/
lemma isFreeGenerator_omegaGen (i : ULift.{u} (Fin 2)) : IsFreeGenerator (omegaGen k i) := by
  have h : (relativeDifferentialsIsoTwist k).symm.hom.app _ (twistGen k i) = omegaGen k i :=
    fromTwist_twistGen k i
  rw [← h]
  exact (isFreeGenerator_twistGen k i).app_hom _

/-- The differential `d(x_{other i} / xᵢ)` of the coordinate is a free generator of
`Ω¹_{ℙ¹/k}` over the chart `D₊(xᵢ)`. -/
lemma isFreeGenerator_sectionsD_coord (i : ULift.{u} (Fin 2)) :
    IsFreeGenerator ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).sectionsD _
      (coord k (i := i) (j := other i))) := by
  have hs : ((sign i : Γ(ProjectiveLine (Spec (.of k)), chart k {i}))) * (sign i : _) = 1 := by
    rw [← Int.cast_mul, sign_mul_self, Int.cast_one]
  have h : (⟨_, _, hs, hs⟩ : Γ(ProjectiveLine (Spec (.of k)), chart k {i})ˣ).1 • omegaGen k i =
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).sectionsD _
        (coord k (i := i) (j := other i)) := by
    rw [omegaGen, Int.cast_smul_eq_zsmul, smul_smul, sign_mul_self, one_smul]
    rfl
  rw [← h]
  exact (isFreeGenerator_omegaGen k i).units_smul _

/-- **`dt` is a free generator of `Ω¹_{ℙ¹/k}` over `Dᵢ(g)`.** -/
theorem isFreeGenerator_sectionsD_polyToChartBasicOpen_X (i : ULift.{u} (Fin 2)) (g : k[X]) :
    IsFreeGenerator ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).sectionsD _
      (polyToChartBasicOpen k i g X)) := by
  rw [polyToChartBasicOpen, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, polyEquivChart_apply, polyToChart, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Scheme.Hom.sectionsD_map]
  exact (isFreeGenerator_sectionsD_coord k i).map _

end AlgebraicGeometry.ProjectiveLine
