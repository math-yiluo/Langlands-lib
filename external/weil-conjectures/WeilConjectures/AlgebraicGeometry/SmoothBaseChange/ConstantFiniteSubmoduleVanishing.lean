/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeColimit
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Vanishing of constant coefficients from all finite submodules

Source: Stacks Project, Tag 0739 (lemma-colimit), applied on affine etale objects;
Tag 0F08, cyclic-coefficient reduction.
(blueprint: lem-sbc-constant-finite-submodule-vanishing)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

-- Scalar restriction reduces finiteness to Mathlib's finite torsion Z-module theorem.
private theorem finite_fg_submodule
    (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (n : ℕ) (hn : n ≠ 0)
    (hM : ∀ x : M, n • x = 0) (N : Submodule (ULift.{u + 1} ℤ) M)
    (hN : N.FG) : Finite N := by
  let : Module (ULift.{u + 1} ℤ) N := N.module
  have : Module.Finite ℤ (ULift.{u + 1} ℤ) := inferInstance
  have : Module.Finite (ULift.{u + 1} ℤ) N := Module.Finite.iff_fg.mpr hN
  have : Module.Finite ℤ N := Module.Finite.trans (ULift.{u + 1} ℤ) N
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hn)⟩, ?_⟩
  apply Subtype.ext
  change (n : ℤ) • (x : M) = 0
  simpa using hM x

/-- Higher direct image of a constant bounded torsion module vanishes if it vanishes
for all finite submodules. The submodule index is allowed to live in the module's universe.

Source: Stacks Project, Tag 0739 (lemma-colimit), and Tag 0F08,
cyclic-coefficient reduction.
(blueprint: lem-sbc-constant-finite-submodule-vanishing)

Proof:
1. Index by the finitely generated submodules of M, ordered by inclusion. The zero
submodule makes this category nonempty and the sum of two finitely generated submodules
is a common upper bound. This is a filtered category in Type (u+1). Its inclusion diagram
has colimit M: every element belongs to its cyclic submodule, and compatible linear maps
from the submodules glue uniquely to a linear map from M.
2. Every finitely generated submodule is finite. If it has k generators, the bound n
makes it a quotient of (Z/n)^k. The source is finite because n is nonzero; hence the
submodule is finite. Each corresponding constant sheaf therefore has zero higher image
by the hypothesis. The constant sheaf functor is a left adjoint, so preserves the union.
3. For q nonnegative, compute higher direct image on affine etale objects of X using
cohomology on their pullbacks to Y. These pullbacks are qcqs. Apply Tag 0739 to their
coherent etale sites, with the filtered index category from step 1. The proof of that
tag uses finite covers and finite intersections; it works in the lifted universe as
well, without shrinking this index category to Type 0. Pullback and sheafification
preserve colimits. Consequently the higher image of the union is the sheafified
filtered colimit of the higher images of these constant sheaves.
4. The latter diagram consists of zero objects, hence its colimit is zero. For q negative,
the right derived pushforward of a sheaf in degree zero is concentrated in nonnegative
degrees, so its degree-q homology is zero directly. The argument includes M=0 and n=1. -/
theorem isZero_higherDirectImage_constant_of_finite_submodules
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (n : ℕ) (hn : n ≠ 0) (hM : ∀ x : M, n • x = 0)
    (hfinite : ∀ (N : Submodule (ULift.{u + 1} ℤ) M), Finite N →
      IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
          (ModuleCat.of (ULift.{u + 1} ℤ) N)))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj M)) :=
  by
    classical
    let R := ULift.{u + 1} ℤ
    let I := {N : Submodule R M // N.FG}
    have : Nonempty I := ⟨⟨⊥, Submodule.fg_bot⟩⟩
    let : ∀ N : I, Module R N.1 := fun N ↦ N.1.module
    let D := ModuleCat.directLimitDiagram (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
      (Module.fgSystem R M)
    let c := ModuleCat.directLimitCocone (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
      (Module.fgSystem R M)
    let H := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (lowerStar (ModuleCat.{u + 1} R) h).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ q
    have : PreservesColimitsOfShape I
        (DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0 ⋙
            (lowerStar (ModuleCat.{u + 1} R) h).rightDerivedFunctorPlus ⋙
              DerivedCategory.Plus.homologyFunctor _ q) :=
      preservesColimitsOfShape_higherDirectImage_large R h q I
    have : PreservesColimitsOfShape I H := by
      dsimp only [H, constantSheaf]
      infer_instance
    have hc : IsColimit c := ModuleCat.directLimitIsColimit _ _
    have hz : IsZero (H.obj c.pt) := (isColimitOfPreserves H hc).isZero_pt
      ((D ⋙ H).isZero (fun N ↦ by
        -- The hypothesis uses the canonical lifted-integer action on N.
        have hmodule : N.1.module = (ULift.module : Module R N.1) := by
          apply Module.ext
          funext r x
          have hr : (r.down : R) = r := by cases r; rfl
          rw [← hr]
          exact Int.cast_smul_eq_zsmul R r.down x
        have he : D.obj N = @ModuleCat.of R _ N.1 _ ULift.module := by
          change @ModuleCat.of R _ N.1 _ N.1.module = _
          rw [hmodule]
        change IsZero (H.obj (D.obj N))
        rw [he]
        exact hfinite N.1 (finite_fg_submodule M n hn hM N.1 N.2)))
    let e : c.pt ≅ M := (Module.fgSystem.equiv R M).toModuleIso
    exact hz.of_iso (H.mapIso e.symm)

end AlgebraicGeometry.Etale
