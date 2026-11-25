/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.Algebra.Homology.ExactCouple.HalfPlane
public import WeilConjectures.Algebra.Homology.ExactCouple.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The truncation couple

Let `v : A ⥤ B` be an additive functor between abelian categories, where `A` has enough
injectives, and let `M` be an object of the bounded below derived category `D⁺(A)`, for instance
a bounded below complex `K`. The canonical truncations `τ_{≤ q} M` form a tower of distinguished
triangles

`τ_{≤ q - 1} M ⟶ τ_{≤ q} M ⟶ Hᵠ(M)[-q] ⟶ (τ_{≤ q - 1} M)[1]`

(`DerivedCategory.Plus.truncLETower`). Applying the triangulated functor `R⁺v` and the
cohomology functors gives an exact couple, the **truncation couple**
(`CategoryTheory.Functor.truncationCouple`), with

`D^{p, q} = H^{p + q}(R⁺v(τ_{≤ q} M))`, `E^{p, q} = H^{p + q}(R⁺v(Hᵠ(M)[-q])) ≅ Rᵖv(Hᵠ(M))`,

written in the coordinates `(p, n) = (p, p + q)` of filtration degree and total degree, so that
`α`, `f`, `g` have degrees `(-1, 0)`, `(2, 1)` and `0`, i.e. bidegrees `(-1, 1)`, `(2, -1)` and
`(0, 0)` in `(p, q)`. If `Hᵠ(M) = 0` for `q < a`, it is a half-plane couple
(`CategoryTheory.Functor.truncationCouple_isHalfPlane`), so it converges to
`H^n(R⁺v(τ_{≤ n} M))`.

## Main definitions

- `DerivedCategory.Plus.truncLETower`: the tower of truncations of an object of `D⁺(A)`.
- `CategoryTheory.Functor.truncationCouple`: the truncation couple.

## Main statements

- `CategoryTheory.Functor.truncationCoupleEIso`,
  `CategoryTheory.Functor.truncationCoupleEIsoRightDerived`: the identification of the
  `E`-objects.
- `CategoryTheory.Functor.truncationCouple_isHalfPlane`,
  `CategoryTheory.Functor.convergesTo_truncationCouple`: convergence.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Triangulated

namespace DerivedCategory.Plus

open _root_.DerivedCategory.Plus.TStructure (t)

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The inequality `(q - 1) + 1 ≤ q + 1` in `EInt`. -/
lemma coe_sub_one_add_one_le (q : ℤ) : (((q - 1 + 1 : ℤ)) : EInt) ≤ ((q + 1 : ℤ) : EInt) := by
  rw [WithBotTop.coe_le_coe]
  omega

/-- The distinguished triangle `τ_{< q} M ⟶ τ_{< q + 1} M ⟶ τ_{≥ q} τ_{< q + 1} M ⟶ ...` of
truncations of `M`, with `τ_{< q} M` written `τ_{< (q - 1) + 1} M`. -/
noncomputable abbrev truncLETriangle (M : Plus A) (q : ℤ) : Triangle (Plus A) :=
  (t.triangleω₁δ ⊥ ((q - 1 + 1 : ℤ) : EInt) ((q + 1 : ℤ) : EInt) bot_le
    (coe_sub_one_add_one_le q)).obj M

/-- The **tower of truncations** of an object `M` of `D⁺(A)`: `X q = τ_{≤ q} M = τ_{< q + 1} M`,
with the distinguished triangles `τ_{≤ q - 1} M ⟶ τ_{≤ q} M ⟶ τ_{≥ q} τ_{≤ q} M ⟶ ...`; the
third object is `Hᵠ(M)[-q]` (`DerivedCategory.Plus.truncLETowerYIso`). -/
noncomputable def truncLETower (M : Plus A) : TriangleTower (Plus A) where
  X q := (t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj M
  Y q := (truncLETriangle M q).obj₃
  mor₁ q := (truncLETriangle M q).mor₁
  mor₂ q := (truncLETriangle M q).mor₂
  mor₃ q := (truncLETriangle M q).mor₃
  distinguished _ := t.triangleω₁δ_distinguished _ _ _ _ _ M

/-- The objects `X q = τ_{< q + 1} M` of the tower of truncations. -/
lemma truncLETower_X (M : Plus A) (q : ℤ) :
    (truncLETower M).X q = (t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj M := rfl

/-- The objects `Y q = τ_{≥ q} τ_{< q + 1} M` of the tower of truncations. -/
lemma truncLETower_Y (M : Plus A) (q : ℤ) :
    (truncLETower M).Y q =
      (t.eTruncGE.obj ((q - 1 + 1 : ℤ) : EInt)).obj
        ((t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj M) := rfl

/-- The third object `τ_{≥ q} τ_{≤ q} M` of the triangles of the tower of truncations is
`Hᵠ(M)[-q]`. -/
noncomputable def truncLETowerYIso (M : Plus A) (q : ℤ) :
    (truncLETower M).Y q ≅ (singleFunctor A q).obj ((homologyFunctor A q).obj M) :=
  eqToIso (by rw [truncLETower_Y, sub_add_cancel]; rfl) ≪≫ (eTruncLTCompETruncGEIso q).app M

/-- If `M` is `≥ a`, then `τ_{≤ q} M = 0` for `q < a`. -/
lemma isZero_truncLETower_X (M : Plus A) (a : ℤ) [M.IsGE a] (q : ℤ) (hq : q < a) :
    IsZero ((truncLETower M).X q) :=
  t.isZero_eTruncLT_obj_obj M a _ (by rw [WithBotTop.coe_le_coe]; omega)

end DerivedCategory.Plus

namespace CategoryTheory.Functor

open _root_.DerivedCategory.Plus.TStructure (t)

open DerivedCategory.Plus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (v : A ⥤ B) [v.Additive]

/-- The tower `R⁺v(τ_{≤ q} M)` of distinguished triangles in `D⁺(B)`. -/
noncomputable abbrev truncationTower (M : DerivedCategory.Plus A) :
    TriangleTower (DerivedCategory.Plus B) :=
  (truncLETower M).map v.rightDerivedFunctorPlus

/-- The **truncation couple** of an additive functor `v : A ⥤ B` (`A` with enough injectives)
and of an object `M` of `D⁺(A)` (for instance a bounded below complex): the exact couple obtained
from the triangles `τ_{≤ q - 1} M ⟶ τ_{≤ q} M ⟶ Hᵠ(M)[-q] ⟶` by applying `R⁺v` and cohomology.
It is indexed by the filtration degree `p` and the total degree `n = p + q`, with

`D^{p, n} = Hⁿ(R⁺v(τ_{≤ n - p} M))`, `E^{p, n} = Hⁿ(R⁺v(Hⁿ⁻ᵖ(M)[p - n]))`

(`CategoryTheory.Functor.truncationCoupleEIso`), `α : D^{p + 1, n} ⟶ D^{p, n}` induced by the
maps `τ_{≤ q} M ⟶ τ_{≤ q + 1} M`, `g : D^{p, n} ⟶ E^{p, n}` induced by the maps of the triangles
and `f : E^{p, n} ⟶ D^{p + 2, n + 1}` the connecting maps. In the coordinates `(p, q)` the maps
`α`, `f`, `g` have bidegrees `(-1, 1)`, `(2, -1)` and `(0, 0)`. This data is an exact couple
(remark `rem-ptr-sp-truncation-couple-1`), by `TriangleTower.exactCoupleTotal`.

(blueprint: `def-sp-truncation-couple`, `rem-ptr-sp-truncation-couple-1`) -/
noncomputable def truncationCouple (M : DerivedCategory.Plus A) :
    ExactCouple B ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  (v.truncationTower M).exactCoupleTotal (DerivedCategory.Plus.homologyFunctor B 0)

/-- The `D`-objects of the truncation couple: `D^{p, n} = Hⁿ(R⁺v(τ_{≤ n - p} M))`. -/
lemma truncationCouple_D (M : DerivedCategory.Plus A) (p n : ℤ) :
    (v.truncationCouple M).D (p, n) = (DerivedCategory.Plus.homologyFunctor B n).obj
      (v.rightDerivedFunctorPlus.obj ((truncLETower M).X (n - p))) := rfl

/-- The `E`-objects of the truncation couple: `E^{p, n} = Hⁿ(R⁺v(Y (n - p)))`. -/
lemma truncationCouple_E (M : DerivedCategory.Plus A) (p n : ℤ) :
    (v.truncationCouple M).E (p, n) = (DerivedCategory.Plus.homologyFunctor B n).obj
      (v.rightDerivedFunctorPlus.obj ((truncLETower M).Y (n - p))) := rfl

/-- The `E`-objects of the truncation couple: `E^{p, n} ≅ Hⁿ(R⁺v(Hᵠ(M)[-q]))` with `q = n - p`.

(blueprint: `def-sp-truncation-couple`) -/
noncomputable def truncationCoupleEIso (M : DerivedCategory.Plus A) (p n : ℤ) :
    (v.truncationCouple M).E (p, n) ≅ (DerivedCategory.Plus.homologyFunctor B n).obj
      (v.rightDerivedFunctorPlus.obj ((singleFunctor A (n - p)).obj
        ((DerivedCategory.Plus.homologyFunctor A (n - p)).obj M))) :=
  (DerivedCategory.Plus.homologyFunctor B n).mapIso
    (v.rightDerivedFunctorPlus.mapIso (truncLETowerYIso M (n - p)))

/-- `Hᵐ(R⁺v(X[-q])) ≅ Hᵐ⁻ᵠ(R⁺v(X[0]))`. -/
noncomputable def homologyRightDerivedFunctorPlusObjSingleIso (X : A) (q m m' : ℤ)
    (h : m' + q = m) :
    (DerivedCategory.Plus.homologyFunctor B m).obj
        (v.rightDerivedFunctorPlus.obj ((singleFunctor A q).obj X)) ≅
      (DerivedCategory.Plus.homologyFunctor B m').obj
        (v.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj X)) :=
  (DerivedCategory.Plus.homologyFunctor B m).mapIso (v.rightDerivedFunctorPlus.mapIso
      (((DerivedCategory.Plus.singleFunctors A).shiftIso (-q) q 0 (by omega)).symm.app X) ≪≫
    (v.rightDerivedFunctorPlus.commShiftIso (-q)).app _) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) m m' (by omega)).app _

/-- The objects `Hᵐ(R⁺v(X[0]))` vanish for `m < 0`. -/
lemma isZero_homologyRightDerivedFunctorPlusObjSingle (X : A) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B m).obj
      (v.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj X))) :=
  v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ 0 hm

/-- The `E`-objects of the truncation couple are the right derived functors of the cohomology
objects of `M`: `E^{p, p + q} ≅ Rᵖv(Hᵠ(M))`.

(blueprint: `def-sp-truncation-couple`) -/
noncomputable def truncationCoupleEIsoRightDerived (M : DerivedCategory.Plus A) (p : ℕ) (q : ℤ) :
    (v.truncationCouple M).E (p, p + q) ≅
      (v.rightDerived p).obj ((DerivedCategory.Plus.homologyFunctor A q).obj M) :=
  v.truncationCoupleEIso M p (p + q) ≪≫ eqToIso (by rw [add_sub_cancel_left]) ≪≫
    v.homologyRightDerivedFunctorPlusObjSingleIso _ q (p + q) p rfl ≪≫
    v.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ p

/-- If `M` has no cohomology in degrees `< a`, the truncation couple is a half-plane couple: with
`q = n - p`, `D^{p, n} = 0` for `q < a` and `E^{p, n} = 0` unless `p ≥ 0` and `q ≥ a`.

(blueprint: `thm-sp-half-plane-convergence`) -/
lemma truncationCouple_isHalfPlane (M : DerivedCategory.Plus A) (a : ℤ) [M.IsGE a] :
    (v.truncationCouple M).IsHalfPlane a where
  isZero_D p n h := by
    rw [truncationCouple_D]
    exact Functor.map_isZero _ (Functor.map_isZero _ (isZero_truncLETower_X M a _ h))
  isZero_E p n h := by
    refine IsZero.of_iso ?_ (v.truncationCoupleEIso M p n)
    obtain h | h := h
    · exact (v.isZero_homologyRightDerivedFunctorPlusObjSingle _ p h).of_iso
        (v.homologyRightDerivedFunctorPlusObjSingleIso _ (n - p) n p (by omega))
    · exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
        (DerivedCategory.Plus.isZero_homology_of_isGE M a _ h)))

/-- **Convergence of the truncation couple.** If `M` has no cohomology in degrees `< a`, the
spectral sequence of the truncation couple, with `E₂^{p, q} = Rᵖv(Hᵠ(M))`, converges to
`Aⁿ = D^{0, n} = Hⁿ(R⁺v(τ_{≤ n} M))`, with the finite filtration
`Fᵖ Aⁿ = im (D^{p, n} ⟶ D^{0, n})`.

(blueprint: `thm-sp-half-plane-convergence`) -/
theorem convergesTo_truncationCouple (M : DerivedCategory.Plus A) (a : ℤ) [M.IsGE a] :
    (v.truncationCouple M).ConvergesTo
      (ExactCouple.halfPlaneι (v.truncationCouple_isHalfPlane M a) (by norm_num))
      (ExactCouple.halfPlaneFiltration (v.truncationCouple_isHalfPlane M a) (by norm_num)) :=
  ExactCouple.convergesTo_halfPlaneFiltration _ _

/-- The truncation `τ_{≤ n} M ⟶ M` induces an isomorphism `Hⁿ(R⁺v(τ_{≤ n} M)) ≅ Hⁿ(R⁺v(M))`,
since `R⁺v(τ_{> n} M)` has no cohomology in degrees `≤ n`. -/
lemma isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLTι
    (M : DerivedCategory.Plus A) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B n).map
      (v.rightDerivedFunctorPlus.map ((t.truncLTι (n + 1)).app M))) := by
  let T := v.rightDerivedFunctorPlus.mapTriangle.obj ((t.triangleLTGE (n + 1)).obj M)
  have hT : T ∈ distTriang _ :=
    v.rightDerivedFunctorPlus.map_distinguished _ (t.triangleLTGE_distinguished (n + 1) M)
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have h₀ : IsZero ((H.shift (n - 1)).obj T.obj₃) :=
    v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ (n + 1) (by omega)
  have h₁ : IsZero ((H.shift n).obj T.obj₃) :=
    v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ (n + 1) (by omega)
  have : Mono ((H.shift n).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T hT (n - 1) n (by omega)).2
      (h₀.eq_of_src _ _)
  have : Epi ((H.shift n).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T hT n).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift n).map T.mor₁)

/-- The abutment `Aⁿ = D^{0, n} = Hⁿ(R⁺v(τ_{≤ n} M))` of the truncation couple is
`Hⁿ(R⁺v(M))`.

(blueprint: `thm-sp-half-plane-convergence`) -/
noncomputable def truncationCoupleAbutmentIso (M : DerivedCategory.Plus A) (n : ℤ) :
    (v.truncationCouple M).D (0, n) ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj (v.rightDerivedFunctorPlus.obj M) :=
  have := v.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLTι M n
  eqToIso (by rw [truncationCouple_D, truncLETower_X, sub_zero]; rfl) ≪≫
    asIso ((DerivedCategory.Plus.homologyFunctor B n).map
      (v.rightDerivedFunctorPlus.map ((t.truncLTι (n + 1)).app M)))

end CategoryTheory.Functor
