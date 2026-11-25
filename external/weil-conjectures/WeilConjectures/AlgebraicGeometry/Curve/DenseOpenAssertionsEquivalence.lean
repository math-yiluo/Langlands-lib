/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveAnnihilator
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveSubPart
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionModulesAgree
import WeilConjectures.AlgebraicGeometry.Curve.FiniteCoefficientAssertions
import WeilConjectures.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The eight curve assertions for constructible torsion abelian sheaves

A constructible torsion abelian sheaf on a curve over an algebraically closed field is killed
by some `n ≥ 1`, so it is the underlying abelian sheaf of a sheaf of `ℤ/n`-modules, and the
eight assertions, which only see the underlying abelian sheaf, hold for it by the curve package
`AlgebraicGeometry.IsCurve.Assertions.of_finite_coefficients`. Consequently the assertions for
`F` and for `j_! j^* F` are equivalent for every open `j`, without any condition on the torsion
of `F`: this is the unconditional form of `AlgebraicGeometry.IsCurve.dense_open_assertions`.

Source: Stacks Project, Theorem 03SC and Lemma 0GJA (blueprint: `app:curve-package`,
`lemma-removing-finitely-many-points`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The underlying abelian sheaf of the `ULift ℤ`-module sheaf attached to an abelian sheaf
`A` is `A` again. -/
private noncomputable def integralUnderlyingIso {X : Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
      ((sheafCompose X.smallEtaleTopology
        ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
          ModuleCat.restrictScalars
            (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom)).obj A) ≅ A :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft A.obj
      ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso) ≪≫
      A.obj.rightUnitor)

/-- **The curve package for constructible torsion abelian sheaves.** Let `k` be algebraically
closed and `(C, F)` a curve coefficient pair over `k` with `F` constructible. Then the eight
assertions `C(C, F)` hold, for `F` viewed as a sheaf of `ULift ℤ`-modules.

Source: Stacks Project, Theorem 03SC (blueprint: `app:curve-package`).

Proof: `C` is quasi-compact, so `F` is killed by some `n ≥ 1`
(`AlgebraicGeometry.CurveCoefficientPair.exists_annihilator_of_constructible`), and it is the
underlying abelian sheaf of a sheaf `M` of `ℤ/n`-modules, constructible as a module sheaf
(`AlgebraicGeometry.Scheme.constructible_torsion_modules_agree`). The curve package
`AlgebraicGeometry.IsCurve.Assertions.of_finite_coefficients` gives `C(C, M)`, and the eight
assertions only depend on the underlying abelian sheaf
(`AlgebraicGeometry.IsCurve.assertions_of_underlying_abelian_iso`). -/
theorem CurveCoefficientPair.assertions_of_constructible {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        P.F)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec
      ((sheafCompose P.C.smallEtaleTopology E).obj P.F) := by
  intro E
  have : IsCurve P.toSpec := P.isCurve
  obtain ⟨n, hn, hkill⟩ := P.exists_annihilator_of_constructible hP
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hT, M, e, -, hM, -⟩ :=
    Scheme.constructible_torsion_modules_agree P.toSpec n hn P.F hkill
  have : Scheme.IsConstructibleSheaf M :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf M).mp (hM.mp hP)
  have : Scheme.IsConstructibleSheaf ((sheafCompose P.C.smallEtaleTopology E).obj P.F) :=
    (Scheme.isConstructibleSheaf_integral_iff P.F hT).mpr hP
  exact IsCurve.assertions_of_underlying_abelian_iso P.toSpec
    (e ≪≫ (integralUnderlyingIso P.F).symm)
    (IsCurve.Assertions.of_finite_coefficients _ P.toSpec M)

/-- The extension by zero `j_! j^* F` of the restriction of a constructible torsion abelian
sheaf `F` on a curve to an open `U` is again constructible: it is the subsheaf in the
open–closed exact sequence `0 → j_! j^* F → F → i_* i^* F → 0`
(`AlgebraicGeometry.CurveCoefficientPair.constructible_sub_part`). -/
private theorem isConstructible_openImmersionLowerShriek {k : Type u} [Field k]
    [IsAlgClosed k] (P : CurveCoefficientPair k) (hP : Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        P.F)) (U : P.C.Opens) :
    P.C.IsTorsionAbelianSheaf ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)) ∧
      Scheme.IsConstructibleEtaleSheafOfSets
        ((sheafCompose P.C.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F))) := by
  have hrange : Set.range U.closedComplement.base = (Set.range U.ι.base)ᶜ := by
    rw [U.range_closedComplement, Scheme.Opens.range_ι]
  let S := Etale.openClosedShortComplex AddCommGrpCat.{u + 1} U.ι U.closedComplement
    (disjoint_range_of_range_eq_compl U.ι U.closedComplement hrange) P.F
  have hS : S.ShortExact :=
    Etale.shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} U.ι U.closedComplement P.F
      hrange
  have : IsCurve P.toSpec := P.isCurve
  obtain ⟨n, hn, hkill⟩ := P.exists_annihilator_of_constructible hP
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have h₁ : n • 𝟙 S.X₁ = 0 := by
    rw [← cancel_mono S.f, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id S.f, ← Preadditive.comp_nsmul]
    exact (congrArg (S.f ≫ ·) hkill).trans comp_zero
  have h₃ : n • 𝟙 S.X₃ = 0 := by
    rw [← cancel_epi S.g, comp_zero, Preadditive.comp_nsmul, Category.comp_id,
      ← Category.id_comp S.g, ← Preadditive.nsmul_comp]
    exact (congrArg (· ≫ S.g) hkill).trans zero_comp
  have hT₁ : P.C.IsTorsionAbelianSheaf S.X₁ :=
    (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
      (Scheme.isTorsion_of_nsmul_id_eq_zero hn h₁)
  have hT₃ : P.C.IsTorsionAbelianSheaf S.X₃ :=
    (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
      (Scheme.isTorsion_of_nsmul_id_eq_zero hn h₃)
  exact ⟨hT₁, CurveCoefficientPair.constructible_sub_part P S.X₁ S.X₃ hT₁ hT₃ S.f S.g S.zero
    hS hP⟩

/-- **Extension by zero from an open does not change the eight assertions**, for a
constructible torsion abelian sheaf. Let `k` be algebraically closed, `(C, F)` a curve
coefficient pair over `k` with `F` constructible and `j : U ⟶ C` an open immersion. Then
`C(C, F)` holds if and only if `C(C, j_! j^* F)` holds, both sheaves viewed as sheaves of
`ULift ℤ`-modules. Unlike `AlgebraicGeometry.IsCurve.dense_open_assertions`, no condition on the
torsion of `F` is needed; and the statement holds for every open `U`, in particular for every
dense open.

Source: Stacks Project, Lemma 0GJA (blueprint: `lemma-removing-finitely-many-points`).

Proof: both sides hold by
`AlgebraicGeometry.CurveCoefficientPair.assertions_of_constructible`; for `j_! j^* F`, which is
torsion and constructible as the subsheaf in the open–closed exact sequence
`0 → j_! j^* F → F → i_* i^* F → 0`, applied to the curve coefficient pair `(C, j_! j^* F)`. -/
theorem IsCurve.assertions_iff_dense_open {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        P.F)) (U : P.C.Opens) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F ↔
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G := by
  intro E F F' G
  obtain ⟨hT, hP'⟩ := isConstructible_openImmersionLowerShriek P hP U
  exact iff_of_true (P.assertions_of_constructible hP)
    (CurveCoefficientPair.assertions_of_constructible
      ⟨P.C, P.toSpec, P.isCurve, F', (Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hT⟩
      hP')

end AlgebraicGeometry
