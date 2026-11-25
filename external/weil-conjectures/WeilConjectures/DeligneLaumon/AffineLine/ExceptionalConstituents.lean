/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.WeilSheaf.AffineLineCohomology
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.GeometricallyConstant

/-!
# Constant constituents on the affine line

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion and let `M ≅ ℚ̄_ℓ(b)` be a constant Weil twist of
the constant sheaf on `U₀`. The underlying sheaf of the direct image `j_*M` is `j̄_*ℚ̄_ℓ ≅ ℚ̄_ℓ`,
the constant sheaf extending uniquely across the boundary, so `j_*M` is a constant twist of the
constant sheaf of the line. Hence `H_c^1(𝔸¹, j_*M) = 0`, since `R Γ_c(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ(-1)[-2]`.
This is the geometrically constant case of Step 4 of the blueprint proof of
`theorem-weight-bound-affine-line`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_iso_directImage_constantTwist`: `j_*M` is a
  constant twist of `ℚ̄_ℓ`.
- `…LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_one_of_iso_constantTwist`:
  the vanishing of `H_c^1(𝔸¹, j_*M)`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- If the sheaf `M` of `D` is a constant twist `ℚ̄_ℓ(b)` of the constant sheaf of `U₀`, then its
direct image `j_*M` is a constant twist `ℚ̄_ℓ(c)` of the constant sheaf of the affine line: its
underlying sheaf is `j̄_*ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
theorem exists_iso_directImage_constantTwist (D : LisseOnDenseOpen k₀ l) {b : (PadicAlgCl l)ˣ}
    (e : D.sheaf ≅ (adicConstant k₀ l D.U).constantTwist b) :
    ∃ c : (PadicAlgCl l)ˣ, Nonempty (D.directImage ≅
      (adicConstant k₀ l (affineLine k₀)).constantTwist c) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have := SmoothOfRelativeDimension.smooth 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  have := connectedSpace_geometricFiber (k₀ := k₀) (Y := affineLine k₀)
  obtain ⟨e₁⟩ := ProEtale.nonempty_adicLowerStar_unit_iso_geometricFiberMap (k₀ := k₀) (l := l) D.j
  refine exists_iso_constantTwist_of_iso_unit ((Scheme.Hom.geometricFiberMap D.j
    (comp_over D.j _))_*ᵃ[l].mapIso (((WeilSheaf.objectProperty k₀ l D.U).ι ⋙
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l D.U)).mapIso e) ≪≫ e₁)

/-- If the sheaf `M` of `D` is a constant twist `ℚ̄_ℓ(b)` of the constant sheaf of `U₀`, then
`H_c^1(𝔸¹, j_*M) = 0`: `j_*M` is a constant twist `ℚ̄_ℓ(c)` of the constant sheaf of the line,
and `H_c^1(𝔸¹, ℚ̄_ℓ(c))` is `H_c^1(𝔸¹, ℚ̄_ℓ) = 0` with a rescaled Frobenius. -/
theorem subsingleton_compactlySupportedCohomology_one_of_iso_constantTwist
    (D : LisseOnDenseOpen k₀ l) {b : (PadicAlgCl l)ˣ}
    (e : D.sheaf ≅ (adicConstant k₀ l D.U).constantTwist b) :
    Subsingleton (D.directImage.compactlySupportedCohomology 1).carrier := by
  obtain ⟨c, ⟨e'⟩⟩ := D.exists_iso_directImage_constantTwist e
  obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_constantTwist
    (adicConstant k₀ l (affineLine k₀)) c 1
  have : Subsingleton (((adicConstant k₀ l (affineLine k₀)).compactlySupportedCohomology
      1).rescale c).carrier :=
    subsingleton_compactlySupportedCohomology_adicConstant_affineLine k₀ l (by norm_num)
  exact ((compactlySupportedCohomologyEquivOfIso e' 1).trans E).toLinearEquiv.toEquiv.subsingleton

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen
