/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomField

/-! # A finite-level estimate for internal Hom of integral reductions -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

set_option hygiene false in
local notation "D(" X ", " R ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} R))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- **The internal hom commutes with reduction modulo a power of a nonzerodivisor** in its second
variable: `RHom(K, L) ⊗ᴸ R ⧸ (vⁿ) ≅ RHom(K, L ⊗ᴸ R ⧸ (vⁿ))`. Both are cones of the multiplication
by `vⁿ` on `RHom(K, L)`, the functor `RHom(K, -)` being triangulated and `R`-linear (the right
adjoint of `K ⊗ᴸ -`). -/
theorem nonempty_iso_reductionModIdeal_spanSingletonPow_derivedHom {R : Type (u + 1)}
    [CommRing R] {X : Scheme.{u}} {v : R} (hv : v ∈ nonZeroDivisors R) (n : ℕ) (K L : D(X, R)) :
    Nonempty ((reductionModIdeal R X (Ideal.span {v} ^ n)).obj
        (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L) ≅
      ((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj
        ((reductionModIdeal R X (Ideal.span {v} ^ n)).obj L)) := by
  let Φ := (derivedHom (ModuleCat.{u + 1} R) X).obj (op K)
  let adj := derivedTensorHomAdjunction (ModuleCat.{u + 1} R) K
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  have := adj.right_adjoint_linear (R := R)
  let FX := (derivedTensor (ModuleCat.{u + 1} R) X).obj L
  let FY := (derivedTensor (ModuleCat.{u + 1} R) X).obj (Φ.obj L)
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hv rfl n
  have h₁ : Φ.mapTriangle.obj (FX.mapTriangle.obj T) ∈ distTriang _ :=
    Φ.map_distinguished _ (FX.map_distinguished _
      (_root_.DerivedCategory.quotPowTriangle_distinguished _ hv rfl n))
  have h₂ : FY.mapTriangle.obj T ∈ distTriang _ :=
    FY.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hv rfl n)
  have hX : (Φ.mapTriangle.obj (FX.mapTriangle.obj T)).mor₁ =
      v ^ n • 𝟙 (Φ.obj (FX.obj T.obj₁)) := by
    change Φ.map (FX.map T.mor₁) = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  have hY : (FY.mapTriangle.obj T).mor₁ = v ^ n • 𝟙 (FY.obj T.obj₁) := by
    change FY.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let w : Φ.obj (FX.obj T.obj₁) ≅ FY.obj T.obj₁ :=
    Φ.mapIso (derivedTensorSingleUnitIso L) ≪≫ (derivedTensorSingleUnitIso (Φ.obj L)).symm
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ h₁ h₂
    (Arrow.isoMk w w (by
      change w.hom ≫ (FY.mapTriangle.obj T).mor₁ =
        (Φ.mapTriangle.obj (FX.mapTriangle.obj T)).mor₁ ≫ w.hom
      rw [hX, hY, Linear.comp_smul, Category.comp_id]
      erw [Linear.smul_comp, Category.id_comp]))
  exact ⟨(Pretriangulated.Triangle.π₃.mapIso e).symm⟩

/-- The finite-level part of integral constructible internal Hom, for a single reduction,
before derived completeness and uniform tower bounds. The Tor bounds are measured after
restriction to `R`. -/
theorem integralFiniteHomEstimate
    {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    [Finite (R ⧸ I)]
    {v : R} (hv : v ∈ nonZeroDivisors R) (hI : I = Ideal.span {v})
    {k : Type u} [Field k] [HasInvertibleExponent (R ⧸ I) (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (n : ℕ)
    {K L : D(X, R)}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b c e : ℤ)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hLt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X c e
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) := by
  subst hI
  have hφ : Function.Surjective (Ideal.Quotient.mk (Ideal.span {v} ^ (n + 1))) :=
    Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {v} ^ (n + 1))) =
      Ideal.span {v ^ (n + 1)} := by
    rw [Ideal.mk_ker, Ideal.span_singleton_pow]
  have hv' : v ^ (n + 1) ∈ nonZeroDivisors R := pow_mem hv _
  have : Finite (R ⧸ Ideal.span {v} ^ (n + 1)) :=
    Ideal.finite_quotient_pow ⟨{v}, by simp⟩ _
  have : HasInvertibleExponent (R ⧸ Ideal.span {v} ^ (n + 1)) (Spec (.of k)) := by
    obtain ⟨N, hN, hNR, hNk⟩ :=
      HasInvertibleExponent.exists_isUnit_natCast (Λ := R ⧸ Ideal.span {v}) (X := Spec (.of k))
    refine ⟨N ^ (n + 1), pow_pos hN _, ?_, by simpa using hNk.pow (n + 1)⟩
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ _
    rwa [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at hNR
  let Kn := (derivedExtendScalars hφ hker X).obj K
  let Ln := (derivedExtendScalars hφ hker X).obj L
  -- the reductions are the restrictions of scalars of the derived base changes
  obtain ⟨eK⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars hφ hker X K
  obtain ⟨eL⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars hφ hker X L
  rw [Ideal.mk_ker] at eK eL
  have hKn : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X Kn :=
    (boundedConstructible_derivedRestrictScalars_iff _ Kn).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eK.symm hK)
  have hLn : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X Ln :=
    (boundedConstructible_derivedRestrictScalars_iff _ Ln).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eL.symm hL)
  -- the Tor amplitude of the derived base changes, over `R ⧸ (vⁿ⁺¹)`
  have hKnt : DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X (a + 1) b Kn := by
    refine torAmplitudeIn_derivedExtendScalars hφ hker hv' ?_
    rw [quotientSingle, Ideal.mk_ker]
    exact hKt
  have hLnt : DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X (c + 1) e Ln := by
    refine torAmplitudeIn_derivedExtendScalars hφ hker hv' ?_
    rw [quotientSingle, Ideal.mk_ker]
    exact hLt
  obtain ⟨hHc, hHt⟩ := boundedConstructible_and_torAmplitudeIn_derivedHom_of_field _ aX d hd
    hKn hKnt hLn hLnt
  -- the reduction of the internal hom is the restriction of scalars of the finite internal hom
  obtain ⟨e₁⟩ := nonempty_iso_reductionModIdeal_spanSingletonPow_derivedHom hv (n + 1) K L
  obtain ⟨e₂⟩ := nonempty_iso_derivedHom_derivedTensor_of_isDerivedBaseChange hφ hker X
    (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hφ hker X K)
    (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hφ hker X L)
  rw [Ideal.mk_ker] at e₂
  let e := e₁ ≪≫ e₂
  refine ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e.symm
    ((boundedConstructible_derivedRestrictScalars_iff _ _).2 hHc),
    (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e.symm ?_⟩
  exact (torAmplitudeIn_derivedRestrictScalars hφ hker hv' hHt).mono (by lia) (by lia)

end AlgebraicGeometry.Etale
