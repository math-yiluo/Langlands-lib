/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization

/-!
# Adic reconstruction of smooth purity

At the integral stage `Λ = 𝒪_E` an object is a normalized system `K = (K_n)_n` of finite-level
objects `K_n ∈ D(Y_ét, 𝒪_E ⧸ 𝔪ⁿ⁺¹)` (`AlgebraicGeometry.Etale.NormalizedTower`), realized as the
derived limit `R lim_n K_n`. The adic purity isomorphism is the realization of the
finite-level purity isomorphisms `γ_{f,K_n}`, which form a morphism of normalized systems by
the finite reduction of purity.

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel`: adic reconstruction.

## Implementation notes

The normalized-system structures of `n ↦ Lf^* K_n(d)[2d]` and `n ↦ Rf^! K_n` (the transition
maps exhibiting each level as the derived base change of the next) need the compatibility of
`Lf^*`, of the twist and of `Rf^!` with a change of coefficient ring, which the repository
does not construct; they are therefore given as normalized systems `S` and `T` together with
identifications `eS`, `eT` of their levels.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_Adic_1 (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section Adic

open Opposite

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} [∀ n : ℕ, Finite (R ⧸ I ^ (n + 1))]
  [∀ n : ℕ, HasTateTwist (R ⧸ I ^ (n + 1))] {X Y : Scheme.{u}} (d : ℤ) (f : X ⟶ Y)
  [HasCompactification f]

/-- The level `Lf^* K_n(d)[2d] ∈ D(X_ét, R ⧸ Iⁿ⁺¹)` of the source of the adic purity map of a
normalized system `K = (K_n)_n` on `Y`. -/
noncomputable abbrev twistShiftPullbackLevel (K : NormalizedTower I Y) (n : ℕ) :
    𝐃(X, R ⧸ I ^ (n + 1)) :=
  (twistShift (R ⧸ I ^ (n + 1)) X d).obj
    ((L((f)^*[ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))])).obj (K.obj n))

/-- The level `Rf^! K_n ∈ D(X_ét, R ⧸ Iⁿ⁺¹)` of the target of the adic purity map of a
normalized system `K = (K_n)_n` on `Y`. -/
noncomputable abbrev upperShriekLevel (K : NormalizedTower I Y) (n : ℕ) :
    𝐃(X, R ⧸ I ^ (n + 1)) :=
  (R(f)^![(R ⧸ I ^ (n + 1))]).obj (K.obj n)

/-- Adic reconstruction (reconstruction step only)

Let `K = (K_n)_n` be a normalized system on `Y` (`AlgebraicGeometry.Etale.NormalizedTower`,
levels `K_n ∈ D(Y_ét, A_n)`, `A_n = R ⧸ Iⁿ⁺¹`, the intended case being `R = 𝒪_E`). Let `S` and
`T` be normalized systems on `X` with levels identified with `Lf^* K_n(d)[2d]` (by `eS`) and
`Rf^! K_n` (by `eT`), and let `γ_n : Lf^* K_n(d)[2d] ≅ Rf^! K_n` be isomorphisms forming a
morphism of normalized systems (`hγ`). Then for any homotopy limits `cS`, `cT` of `S` and `T`
there is an isomorphism `e : cS.pt ≅ cT.pt` reducing to `γ_n` at every level `n`:

```
  cS.pt --------- e ---------> cT.pt
    |                            |
   π_n                          π_n
    v                            v
   S_n -- eS ≫ γ_n ≫ eT⁻¹ --> T_n
```

This is only the reconstruction step of the blueprint statement: that the finite-coefficient
purity maps `γ_{f,K_n}` form a morphism of normalized systems (the finite reduction of purity,
`proposition-compatibility-purity-change-coefficients`) is assumed as `hγ`, although it is the first
half of the blueprint's conclusion; the points `cS.pt`, `cT.pt` are arbitrary homotopy limits of `S`
and `T`, not identified with `Lf^* K(d)[2d]` and `Rf^! K`; and `f` enters only through the levels.
The proof is `AlgebraicGeometry.Etale.NormalizedTower.exists_iso_of_isHomotopyLimit`. -/
theorem exists_iso_realization_twistShiftPullbackLevel (K : NormalizedTower I Y)
    (S T : NormalizedTower I X) (eS : ∀ n : ℕ, S.obj n ≅ twistShiftPullbackLevel d f K n)
    (eT : ∀ n : ℕ, T.obj n ≅ upperShriekLevel f K n)
    (γ : ∀ n : ℕ, twistShiftPullbackLevel d f K n ≅ upperShriekLevel f K n)
    (hγ : ∀ n : ℕ, S.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom =
      (eS (n + 1) ≪≫ γ (n + 1) ≪≫ (eT (n + 1)).symm).hom ≫ T.map n)
    {cS : Cone S.restrict} (hcS : Pretriangulated.IsHomotopyLimit cS)
    {cT : Cone T.restrict} (hcT : Pretriangulated.IsHomotopyLimit cT) :
    ∃ e : cS.pt ≅ cT.pt, ∀ n : ℕ, e.hom ≫ cT.π.app (Opposite.op n) =
      cS.π.app (Opposite.op n) ≫ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom :=
  NormalizedTower.exists_iso_of_isHomotopyLimit S T _ hγ hcS hcT

end Adic

end Etale

end AlgebraicGeometry
