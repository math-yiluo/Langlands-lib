/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Curve.PowerMapPullback

/-!
# Primitive-root trivializations commute with field extension

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, compatible primitive-root trivializations
(blueprint: lem-sc-root-trivialization-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, compatible primitive roots in the proper case
(blueprint: lem-sc-root-trivialization-base-change).

Proof: compose both sides with the inclusion of roots of unity into Gm. The defining
commutative square of φ replaces its first component by the units comparison after the
pulled-back inclusion. The original trivialization sends a locally constant class a to
ζ^a. Pullback of units preserves powers and sends ζ to algebraMap k K ζ, so both composites
send a to (algebraMap k K ζ)^a. This equality can be checked on constant presheaf sections,
because the constant sheaf is their sheafification and pullback commutes with sheafification.
The roots-of-unity inclusion is a monomorphism, so cancel it. No smoothness, connectedness,
properness or algebraic closedness is needed for this identity. For n = 1 the constant and
roots-of-unity sheaves are zero and the identity still holds. -/
theorem constant_root_trivialization_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (n : ℕ) [NeZero n]
    (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (hζK : IsPrimitiveRoot (algebraMap k K ζ) n)
    (φ : ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).mapShortComplex.obj
        (C.kummerSequence n)) ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerSequence n)
    (hφ : φ.τ₂ = upperStarGmSheafToGmSheaf
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map
        (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom ≫ φ.τ₁ =
      (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) ≫
      ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZModIsoRootsOfUnitySheaf n
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom := by
  let P := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let π : P ⟶ C := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let g : P ⟶ Spec (.of K) :=
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let uC : IsUnit (((ΓSpecIso (.of k)).inv ≫ f.appTop) ζ) :=
    (hζ.isUnit (NeZero.ne n)).map _
  let uP : IsUnit (((ΓSpecIso (.of K)).inv ≫ g.appTop) (algebraMap k K ζ)) :=
    (hζK.isUnit (NeZero.ne n)).map _
  have huC : uC.unit ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow,
      hζ.pow_eq_one, map_one, Units.val_one])
  have huP : uP.unit ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow,
      hζK.pow_eq_one, map_one, Units.val_one])
  have hu : Units.map π.appTop.hom.toMonoidHom uC.unit = uP.unit := by
    apply Units.ext
    change π.appTop (uC.unit : Γ(C, ⊤)) = (uP.unit : Γ(P, ⊤))
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    change ((ΓSpecIso (.of k)).inv ≫ f.appTop ≫ π.appTop) ζ =
      ((CommRingCat.ofHom (algebraMap k K)) ≫ (ΓSpecIso (.of K)).inv ≫ g.appTop) ζ
    congr 1
    rw [← Hom.comp_appTop,
      show π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) from
        pullback.condition,
      Hom.comp_appTop, ← ΓSpecIso_inv_naturality_assoc]
  apply (cancel_mono (kernel.ι (n • 𝟙 P.gmSheaf))).1
  change _ ≫ φ.τ₁ ≫ (P.kummerSequence n).f = _
  rw [φ.comm₁₂, hφ]
  change (Etale.upperStar AddCommGrpCat.{u + 1} π).map
      (C.constantZModToRootsOfUnitySheaf n uC.unit huC) ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} π).map
      (kernel.ι (n • 𝟙 C.gmSheaf)) ≫ upperStarGmSheafToGmSheaf π = _
  rw [← Functor.map_comp_assoc]
  change (Etale.upperStar AddCommGrpCat.{u + 1} π).map
      (C.constantZModToRootsOfUnitySheaf n uC.unit huC ≫
        kernel.ι (n • 𝟙 C.gmSheaf)) ≫ upperStarGmSheafToGmSheaf π =
    _ ≫ P.constantZModToRootsOfUnitySheaf n uP.unit huP ≫
      kernel.ι (n • 𝟙 P.gmSheaf)
  simp only [constantZModToRootsOfUnitySheaf, kernel.lift_ι]
  exact constantZModToGmSheaf_pullback π n uC.unit huC uP.unit huP hu

end AlgebraicGeometry
