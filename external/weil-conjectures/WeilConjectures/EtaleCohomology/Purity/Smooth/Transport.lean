/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

Smooth purity is proved at the finite coefficient stage in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`. This file records what the three
remaining coefficient stages of the `ℓ`-adic formalism need: the adic category over `𝒪_E`, its
rationalization over `E`, and the colimit over finite extensions `E/ℚ_ℓ` giving `ℚ̄_ℓ`.

In this repository the `𝒪_E` stage is the derived-complete subcategory
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral` of the derived category of sheaves
of `𝒪_E`-modules, and the `E` stage is its rationalization
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`.

## Implementation notes

The statement here is that `Rf^!` preserves derived completeness, which is what makes the
`𝒪_E` stage a stage at all. The transport of the purity isomorphism itself is in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction` (compatibility with the finite
reductions) and `AlgebraicGeometry.Etale.NormalizedTower.exists_iso_of_isHomotopyLimit` (the
realization at the `𝒪_E` stage of a levelwise isomorphism of normalized systems); the smooth
traces are in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Trace`. The purity isomorphism cannot be read
off `proposition-smooth-purity-finite-coefficients` at `Λ = 𝒪_E`: in the étale model `Lf^* K` of a
derived complete `K` need not be derived complete (the constant sheaf `𝒪_E` on `𝔾_m` over an
algebraically closed field is not), whereas `Rf^! K` is.

## Main statements

- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`

## Proof

Derived complete objects are those receiving no nonzero map from an object on which a
uniformizer `ϖ` of `𝒪_E` acts invertibly
(`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A map `L ⟶ Rf^! K` is adjoint to a
map `Rf_! L ⟶ K`, and `ϖ` acts invertibly on `Rf_! L` if it does on `L`, since `Rf_!` is
`𝒪_E`-linear.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E] {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsSeparated f]
  [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_Transport_1 (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

omit [IsSeparated f] in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Smooth purity over `𝒪_E`, `E` and
`ℚ̄_ℓ`

**`Rf^!` preserves derived completeness.** Let `f : X ⟶ Y` be smooth separated of pure
relative dimension `d` and let `Λ = 𝒪_E` be the integral coefficient stage. Then `Rf^!`
carries derived-complete objects of `D(Y_ét, 𝒪_E)` to derived-complete objects of
`D(X_ét, 𝒪_E)`, so that it restricts to the adic categories `D_comp(−, 𝒪_E)` in which the
`ℓ`-adic formalism is typed. The exceptional inverse image `Rf^!` at the integral stage is the
right adjoint of `Rf_!`, whose existence is assumed here: the instance
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` only covers finite coefficients.

The purity isomorphism `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` at the adic stage, realized from the
finite-level purity isomorphisms, is their realization
(`AlgebraicGeometry.Etale.NormalizedTower.exists_iso_of_isHomotopyLimit`). -/
theorem derivedCompleteIntegral_rightDerivedUpperShriek
    [(R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).IsLeftAdjoint]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).rightAdjoint.obj
        K) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  rw [DerivedCategory.derivedCompleteIntegral,
    DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hK ⊢
  intro L φ (hL : IsIso (ϖ • 𝟙 L))
  let adj := Adjunction.ofIsLeftAdjoint
    (R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])
  have hL' : DerivedCategory.smulInvertible Y.smallEtaleTopology ϖ
      ((R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj L) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← (R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).map_id,
      ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv L K).apply_symm_apply φ, hK ((adj.homEquiv L K).symm φ) hL',
    Adjunction.homEquiv_unit,
    Functor.map_zero, comp_zero]

end Etale

end AlgebraicGeometry
