/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier

/-!
# The geometric multiplications of the affine line

For `a ∈ k̄` the multiplication `x ↦ a x` of the geometric affine line `𝔸¹_{k̄}`
(`AlgebraicGeometry.affineLine.geometricSMul`) is multiplicative in `a`, is the identity for
`a = 1`, absorbs the base change of a multiplication by an element of `k₀`, and is an
automorphism for `a ≠ 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] [Finite k₀]

namespace affineLine


/-- The constant function `a ∈ k̄` on the geometric affine line. -/
noncomputable abbrev geometricConst (a : AlgebraicClosure k₀) :
    Γ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber, ⊤) :=
  (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure.appTop
    ((Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom a)

omit [Finite k₀] in
lemma geometricConst_mul (a b : AlgebraicClosure k₀) :
    geometricConst k₀ (a * b) = geometricConst k₀ a * geometricConst k₀ b := by
  simp [geometricConst]

omit [Finite k₀] in
lemma geometricConst_one : geometricConst k₀ 1 = 1 := by
  simp [geometricConst]

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma geometricSMul_comp_geometricFiberToAlgebraicClosure (a : AlgebraicClosure k₀) :
    geometricSMul k₀ a ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
  pullback.lift_snd _ _ _

omit [Finite k₀] in
lemma geometricSMul_comp_geometricFiberProj (a : AlgebraicClosure k₀) :
    geometricSMul k₀ a ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      AffineSpace.homOfVector
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
          (Scheme.specAlgebraicClosure k₀).hom)
        fun _ ↦ geometricConst k₀ a *
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
            (AffineSpace.coord _ PUnit.unit) :=
  pullback.lift_fst _ _ _

omit [Finite k₀] in
@[simp]
lemma geometricSMul_appTop_geometricConst (a b : AlgebraicClosure k₀) :
    (geometricSMul k₀ a).appTop (geometricConst k₀ b) = geometricConst k₀ b := by
  rw [geometricConst, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    geometricSMul_comp_geometricFiberToAlgebraicClosure]

omit [Finite k₀] in
@[simp]
lemma geometricSMul_appTop_coord (a : AlgebraicClosure k₀) :
    (geometricSMul k₀ a).appTop
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
          (AffineSpace.coord _ PUnit.unit)) =
      geometricConst k₀ a *
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
          (AffineSpace.coord _ PUnit.unit) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, geometricSMul_comp_geometricFiberProj,
    AffineSpace.homOfVector_appTop_coord]

omit [Finite k₀] in
/-- `x ↦ b (a x)` is `x ↦ (a b) x`. -/
lemma geometricSMul_comp_geometricSMul (a b : AlgebraicClosure k₀) :
    geometricSMul k₀ a ≫ geometricSMul k₀ b = geometricSMul k₀ (a * b) := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ (by simp)
  rw [Category.assoc, geometricSMul_comp_geometricFiberProj, AffineSpace.comp_homOfVector,
    geometricSMul_comp_geometricFiberProj]
  refine AffineSpace.hom_ext (by simp) fun _ ↦ ?_
  simp only [AffineSpace.homOfVector_appTop_coord, Function.comp_apply, map_mul,
    geometricSMul_appTop_geometricConst, geometricSMul_appTop_coord, geometricConst_mul]
  ring

omit [Finite k₀] in
/-- `x ↦ 1 x` is the identity. -/
lemma geometricSMul_one : geometricSMul k₀ 1 = 𝟙 _ := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ (by simp)
  rw [geometricSMul_comp_geometricFiberProj, Category.id_comp]
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [AffineSpace.homOfVector_over, Scheme.Hom.geometricFiber_condition]
  · simp [geometricConst_one]

omit [Finite k₀] in
/-- For `a ≠ 0` the multiplication by `a` is an automorphism, with inverse the multiplication by
`a⁻¹`. -/
lemma isIso_geometricSMul {a : AlgebraicClosure k₀} (ha : a ≠ 0) :
    IsIso (geometricSMul k₀ a) :=
  ⟨geometricSMul k₀ a⁻¹, by rw [geometricSMul_comp_geometricSMul, mul_inv_cancel₀ ha,
    geometricSMul_one], by rw [geometricSMul_comp_geometricSMul, inv_mul_cancel₀ ha,
    geometricSMul_one]⟩

omit [Finite k₀] in
/-- The geometric multiplication by `a ∈ k̄` followed by the base change of the multiplication
by `c ∈ k₀` is the geometric multiplication by `a c`. -/
lemma geometricSMul_comp_geometricFiberMap_smul (a : AlgebraicClosure k₀) (c : k₀) :
    geometricSMul k₀ a ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ c)
      (comp_over (affineLine.smul k₀ c) _) =
        geometricSMul k₀ (a * algebraMap k₀ (AlgebraicClosure k₀) c) := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, geometricSMul_comp_geometricFiberProj, affineLine.smul,
      AffineSpace.smul, AffineSpace.comp_homOfVector, geometricSMul_comp_geometricFiberProj]
    refine AffineSpace.hom_ext (by simp) fun _ ↦ ?_
    simp only [AffineSpace.homOfVector_appTop_coord, Function.comp_apply, map_mul,
      geometricConst_mul]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have : (Scheme.specAlgebraicClosure k₀).hom.appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom c) =
        (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom
          (algebraMap k₀ (AlgebraicClosure k₀) c) := by
      simp only [Scheme.specAlgebraicClosure, Over.mk_hom]
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    erw [this]
    ring
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
    simp

end affineLine

end AlgebraicGeometry
