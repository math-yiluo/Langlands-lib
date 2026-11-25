/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Compactly supported cohomology of a finite scheme

If `Z₀` is finite over `k₀`, the compactly supported cohomology `H_c^r(Z, G)` of a Weil sheaf `G`
on `Z₀` vanishes for `r ≠ 0`: for `r > 0` the higher direct images with compact support along
the quasi-finite structure morphism vanish, and for `r < 0` the direct image with compact support
of a sheaf is concentrated in nonnegative degrees, being the right derived pushforward of the
extension by zero of a sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- *Cohomology of a finite boundary.* If `X` is finite over `k₀`, then the compactly supported
cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on `X` vanishes for `r ≠ 0`: after geometric
base change `X` becomes a finite discrete space, whose cohomology is concentrated in degree
zero. For `r > 0` this is the vanishing of the higher direct images with compact support along
the quasi-finite structure morphism, for `r < 0` the concentration of the direct image of a sheaf
in nonnegative degrees. The blueprint states this for `G` with stalk weights at most some `w`;
the weights play no role.
(blueprint: `lemma-extreme-degrees-affine-curve`) -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  apply WeilSheaf.subsingleton_globalSections_of_isZero
  rcases hr.lt_or_gt with hr | hr
  · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G hr
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr.le
    exact isZero_higherLowerShriek_of_quasiFinite (X ↘ Spec (CommRingCat.of k₀)) n
      (by exact_mod_cast hr) G

end AlgebraicGeometry
