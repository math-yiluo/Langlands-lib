/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsEpi
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Brauer pullback to the reduction of a curve

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its cohomology
claim. (blueprint: lem-sc-brauer-reduction-injection)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Pullback to the reduction is injective on the cohomological Brauer group of a curve.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-second-kummer-divisors/
lem-sc-brauer-zero-all-curves.md, Proof, Step 1 and the following Claim.
(blueprint: lem-sc-brauer-reduction-injection)

Proof: finite type over a field makes C Noetherian, so its coherent nilradical N has
N^m = 0 for some m. For every affine etale V over C, flatness identifies the pullback of
N with the ideal of V_red, since an etale scheme over C_red is reduced. Lifting units
modulo a nilpotent ideal gives the exact sequence
1 → 1 + N → G_m,C → i_* G_m,C_red → 1 for i : C_red → C.
For j ≥ 1 the map 1 + a ↦ a identifies (1 + N^j)/(1 + N^(j+1)) with the additive
quasi-coherent sheaf (N^j/N^(j+1))_et: the cross term ab lies in N^(j+1).
Every quasi-coherent etale sheaf on C has zero H^q for q ≥ 2. Indeed a finite affine
cover has affine intersections by separatedness; affine etale vanishing and the Cech
spectral sequence identify etale cohomology with Zariski cohomology, which vanishes
above the dimension of the Noetherian scheme C. Descending induction from N^m = 0,
using the long exact sequences of this filtration, gives H^2(C, 1 + N) = 0.
The long exact sequence for units therefore injects H^2(C, G_m) into
H^2(C, i_* G_m,C_red). Exact finite pushforward identifies the latter with
H^2(C_red, G_m). The resulting map is the canonical pullback written below.
This also covers reduced, zero-dimensional, disconnected and empty curves. -/
theorem injective_brauer_pullback_reduction {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Function.Injective (fun x : C.CohomologicalBrauerGroup ↦
      Sheaf.H.map (Scheme.upperStarGmSheafToGmSheaf C.nilradical.subschemeι) 2
        (Etale.cohomologyMap C.nilradical.subschemeι C.gmSheaf 2 x)) := by
  let i := C.nilradical.subschemeι
  let φ := Scheme.upperStarGmSheafToGmSheaf i
  have : Surjective i :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C).2.2.1
  have : IsUniversalHomeomorphism i := {}
  have : Epi φ := Scheme.epi_upperStarGmSheafToGmSheaf_reduction C
  have : Subsingleton (Sheaf.H (Limits.kernel φ) 2) :=
    subsingleton_H_two_reduction_units_kernel f
  let S := ShortComplex.mk (Limits.kernel.ι φ) φ (Limits.kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hinj : Function.Injective (Sheaf.H.map φ 2) := by
    apply (injective_iff_map_eq_zero (Sheaf.H.map φ 2)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := (Sheaf.H.exact_map_map hS 2 x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact hinj.comp (Etale.cohomologyMap_bijective i C.gmSheaf 2).1

end AlgebraicGeometry.IsCurve
