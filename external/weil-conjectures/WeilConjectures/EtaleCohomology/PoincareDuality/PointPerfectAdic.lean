/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness

/-!
# The global sections are perfect at the point: the `ℚ̄_ℓ` stage

Let `k` be an algebraically closed field, `ℓ` different from its characteristic, and `X` a
separated scheme of finite type over `k`. For a pro-étale complex `K` on `X` with constructible
`ℓ`-adic cohomology sheaves, the complexes `RΓ(X, K)` and `RΓ_c(X, K)`, and their duals, are
perfect complexes of `ℚ̄_ℓ`-vector spaces (blueprint `lemma-perfect-complexes-geometric-point`, the
`ℚ̄_ℓ` stage of `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`):

- `AlgebraicGeometry.ProEtale.isPerfect_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_rightDerivedGlobalSections_adic`.

The derived pushforward to `Spec k` of an object of `D^b_c(X, ℚ̄_ℓ)` is in `D^b_c(Spec k, ℚ̄_ℓ)` by
the pro-étale finiteness theorem (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`),
and the global sections of such an object are perfect
(`AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed`).
These statements are in a separate file because the proof of the finiteness theorem imports
the finite stages of `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Adic

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsAlgClosed k] [Fact (ringChar k ≠ l)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

omit [IsSeparated aX] [LocallyOfFiniteType aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**`RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of the
algebraically closed field `k`. For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the compactly supported cohomology
`RΓ_c(X, K)` is a perfect complex of `ℚ̄_ℓ`-vector spaces: bounded with finite dimensional
cohomology. For the compactification `X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`, the extension by zero
`j_! K` is again in `D^b_c(X̄, ℚ̄_ℓ)`, hence so is `Rā_* j_! K ∈ D^b_c(Spec k, ℚ̄_ℓ)` by the
finiteness theorem (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`), all of this
computed on the underlying sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso`); and the
global sections of an object of `D^b_c(Spec k, ℚ̄_ℓ)` are perfect
(`AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed`). -/
theorem isPerfect_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect := by
  let c := HasCompactification.compactification aX
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have hK' : DerivedCategory.boundedAdicConstructible l c.Z
      ((c.i)_!ᵃ[l].mapDerivedCategory.obj K) :=
    ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
      (adicConstructibleSheaf l c.Z).prop_of_iso
        (((c.i)_!ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app K)
        ((hK.2 n).openImmersionLowerShriek c.i)⟩
  have hM : DerivedCategory.boundedAdicConstructible l (Spec (.of k))
      ((c.g)_*ᵃ[l].rightDerivedFunctor.obj ((c.i)_!ᵃ[l].mapDerivedCategory.obj K)) :=
    finiteLowerStar_of_bounded c.g
      (fun _ hF ↦ finiteLowerStar_singleFunctor (𝟙 _) c.g (Fact.out : ringChar k ≠ l) hF)
      _ hK'.1 hK'.2
  have e₁ : (c.i)_!open[WeilCoefficients.{u} l].mapDerivedCategory.obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K) ≅
      (ProEtale.AdicSheaf.forget c.Z).mapDerivedCategory.obj
        ((c.i)_!ᵃ[l].mapDerivedCategory.obj K) :=
    (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
      (Functor.mapDerivedCategoryNatIso
        (asIso (adicOpenImmersionLowerShriekComparison l c.i))).app K ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app K
  exact (isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed l _ hM).of_iso
    ((rightDerivedGlobalSections _ _).mapIso
      (((mapDerivedCategoryForgetCompRightDerivedLowerStarIso l c.g).app _).symm ≪≫
        ((c.g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor.mapIso e₁.symm))

omit [HasCompactification aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**`RΓ(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of the
algebraically closed field `k`. For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the cohomology `RΓ(X, K)` is a
perfect complex of `ℚ̄_ℓ`-vector spaces: `RΓ(X, K) ≅ RΓ(Spec k, Ra_{X*} K)` (Leray), and
`Ra_{X*} K ∈ D^b_c(Spec k, ℚ̄_ℓ)` by the finiteness theorem
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`). -/
theorem isPerfect_rightDerivedGlobalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect := by
  have hM : DerivedCategory.boundedAdicConstructible l (Spec (.of k))
      ((aX)_*ᵃ[l].rightDerivedFunctor.obj K) :=
    finiteLowerStar_of_bounded aX
      (fun _ hF ↦ finiteLowerStar_singleFunctor (𝟙 _) aX (Fact.out : ringChar k ≠ l) hF)
      _ hK.1 hK.2
  have : ((aX)_*[WeilCoefficients.{u} l]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction _ aX).preservesKInjectiveComplexes
  exact (isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed l _ hM).of_iso
    ((rightDerivedGlobalSections _ _).mapIso
      ((mapDerivedCategoryForgetCompRightDerivedLowerStarIso l aX).app K).symm ≪≫
      (Functor.rightDerivedFunctorCompIso' _ _
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) aX)).app _)

omit [IsSeparated aX] [LocallyOfFiniteType aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**The dual of `RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((ihom ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_adic l aX K hK).ihom_unit

omit [HasCompactification aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point.

**The dual of `RΓ(X, K)` is perfect at `ℚ̄_ℓ`.** -/
theorem isPerfect_ihom_rightDerivedGlobalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((ihom ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections_adic l aX K hK).ihom_unit


/-- Blueprint `lemma-perfect-complexes-geometric-point`: Point perfectness of global sections, the
stage `ℚ̄_ℓ`.

For `ℓ` different from the characteristic of `k` and `K ∈ D^b_c(X, ℚ̄_ℓ)`, the four complexes
`RΓ(X, K)`, `RΓ_c(X, K)` and their duals are perfect complexes of `ℚ̄_ℓ`-vector spaces: bounded
with finite-dimensional cohomology. -/
theorem isPerfect_globalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
        ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect ∧
      ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
        ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect ∧
      ((ihom ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
        ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj (𝟙_ _)).IsPerfect ∧
      ((ihom ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
        ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj (𝟙_ _)).IsPerfect :=
  ⟨isPerfect_rightDerivedGlobalSections_adic l aX K hK,
    isPerfect_compactlySupportedGlobalSections_adic l aX K hK,
    isPerfect_ihom_rightDerivedGlobalSections_adic l aX K hK,
    isPerfect_ihom_compactlySupportedGlobalSections_adic l aX K hK⟩

end Adic

end ProEtale

end AlgebraicGeometry
