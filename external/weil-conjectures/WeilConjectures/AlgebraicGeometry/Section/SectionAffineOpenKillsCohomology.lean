/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.FractionZeroTensorPower

/-!
# A power of a section kills a positive cohomology class

## References

* Stacks Project, Cohomology of Schemes, Lemma 01XR
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- If the nonvanishing open of a section of an invertible module is affine, every positive
cohomology class of a quasi-coherent module is killed by some tensor power of that section.
The map is induced by `F ≅ F ⊗ 𝒪_X ⟶ F ⊗ L^{⊗ e}`, with second factor `s^{⊗ e}`. -/
theorem exists_tensorPowSection_cohomology_eq_zero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus L s) (hAffine : IsAffineOpen U)
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p)
    (xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    ∃ e : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace p).map
      ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e) xi = 0 := by
  obtain ⟨V, hV, e, _⟩ := invertS_cohomology X L F s p
  have hVU : V = U := SetLike.coe_injective (hV.trans hU.symm)
  subst V
  let : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F) :=
    subsingleton_openModuleCohomology_of_isAffineOpen X F U hAffine p hp
  have hsub : Subsingleton (CohomologyFractionPresentation L F s p ⊤) :=
    ⟨fun x y ↦ e.injective (Subsingleton.elim (e x) (e y))⟩
  exact exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions X L F s p hsub xi

end AlgebraicGeometry.Scheme.Modules
