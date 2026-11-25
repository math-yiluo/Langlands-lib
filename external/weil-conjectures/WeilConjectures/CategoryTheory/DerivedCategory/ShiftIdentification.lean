/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Shift identification for bounded below right derived functors

Source: Weil conjectures blueprint, chap-Proper-base-change,
theorem-proper-base-change-classical-pro, lemma lem-sp-shift-identification; Stacks Project, Tags
05SU, 015A and 05TC (blueprint: lem-sp-shift-identification).

The three statements specify the shift comparison, its composition with the ordinary
right-derived-functor comparison in nonnegative degrees, and vanishing in negative degrees.
The shift of the single complex in degree zero is used literally, so that `X[-q]` means
`X` in degree `q`. Natural isomorphisms have domain `CochainComplex.Plus C`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive]

/-- The composite of the shift comparison for `RF` and cohomology of a shift is an
isomorphism natural in the bounded below complex `K`.
Source: blueprint lem-sp-shift-identification, part 1; Stacks Tag 05SU and Homology,
Definitions 011G and 011H (blueprint: lem-sp-shift-identification).

Proof: (1) Put `X = H^q(K)`. The complex `X[0][-q]` is `X` in degree `q`, with zero
elsewhere and zero differential, and is bounded below. (2) By
lem-weil-pbc-derived-direct-image-triangulated the resolution comparison gives the natural
shift isomorphism `sigma`; iterate its degree-one form, using inverses for negative shifts.
(3) By lem-sp-derived-cohomology-shift, `H^(p+q)(M[-q])` identifies naturally with `H^p(M)`.
(4) Apply cohomology to `sigma` and compose with this identification. Functors preserve
isomorphisms, and both factors are natural in `X`; precompose with `K ↦ H^q(K)`. -/
theorem exists_rightDerived_shift_identification [PreservesFiniteLimits F] (p q : ℤ) :
    let Hq := CochainComplex.Plus.ι C ⋙
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
    let S := DerivedCategory.Plus.singleFunctor C 0
    let RF := F.rightDerivedFunctorPlus
    let H := DerivedCategory.Plus.homologyFunctor D 0
    ∃ e : Hq ⋙ S ⋙ shiftFunctor (DerivedCategory.Plus C) (-q) ⋙ RF ⋙ H.shift (p + q) ≅
        Hq ⋙ S ⋙ RF ⋙ H.shift p,
      ∀ K : CochainComplex.Plus C,
        e.app K = (H.shift (p + q)).mapIso
            ((RF.commShiftIso (-q)).app (S.obj (Hq.obj K))) ≪≫
          (H.shiftIso (-q) (p + q) p (by omega)).app (RF.obj (S.obj (Hq.obj K))) := by
  dsimp only
  let Hq := CochainComplex.Plus.ι C ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
  let S := DerivedCategory.Plus.singleFunctor C 0
  let RF := F.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor D 0
  refine ⟨isoWhiskerLeft (Hq ⋙ S)
      (isoWhiskerRight (RF.commShiftIso (-q)) (H.shift (p + q))) ≪≫
    isoWhiskerLeft (Hq ⋙ S ⋙ RF) (H.shiftIso (-q) (p + q) p (by omega)), ?_⟩
  intro K
  apply Iso.ext
  rfl

/-- In nonnegative degree, the same composite followed by the canonical comparison with
ordinary right derived functors is an isomorphism natural in `K`.
Source: blueprint lem-sp-shift-identification, part 2; Stacks Definition 015A,
Lemmas 05TH, 05TI and Proposition 05TA (blueprint: lem-sp-shift-identification).

Proof: carry out steps (1)--(4) of part 1 with `p = n`. (5) By
lem-sp-derived-functor-single-identification, an injective resolution of `X` is also a
K-injective resolution of `X[0]`. Thus `H^n(RF(X[0])) ≅ R^n F(X)`, naturally in `X`, by
computing both sides on that resolution using def-sp-left-exact-additive. Compose this
canonical isomorphism with the composite in part 1 and precompose with `K ↦ H^q(K)`. -/
theorem exists_rightDerived_shift_identification_nonneg [PreservesFiniteLimits F]
    (n : ℕ) (q : ℤ) :
    let Hq := CochainComplex.Plus.ι C ⋙
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
    let S := DerivedCategory.Plus.singleFunctor C 0
    let RF := F.rightDerivedFunctorPlus
    let H := DerivedCategory.Plus.homologyFunctor D 0
    ∃ e : Hq ⋙ S ⋙ shiftFunctor (DerivedCategory.Plus C) (-q) ⋙ RF ⋙
          H.shift ((n : ℤ) + q) ≅ Hq ⋙ F.rightDerived n,
      ∀ K : CochainComplex.Plus C,
        e.app K = (H.shift ((n : ℤ) + q)).mapIso
            ((RF.commShiftIso (-q)).app (S.obj (Hq.obj K))) ≪≫
          (H.shiftIso (-q) ((n : ℤ) + q) n (by omega)).app
            (RF.obj (S.obj (Hq.obj K))) ≪≫
          F.homologyRightDerivedFunctorPlusObjSingleFunctorIso (Hq.obj K) n := by
  dsimp only
  let Hq := CochainComplex.Plus.ι C ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
  obtain ⟨e, he⟩ := F.exists_rightDerived_shift_identification (n : ℤ) q
  refine ⟨e ≪≫ isoWhiskerLeft Hq
    (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n), ?_⟩
  intro K
  rw [NatIso.trans_app, he K]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  rfl

/-- All three objects in the shift identification vanish when `p < 0`. The last term
spells out the convention `R^p F = 0` for negative `p`, since `Functor.rightDerived` takes
a natural-number index. A zero object is expressed by `IsZero`, rather than equality of
chosen objects.
Source: blueprint lem-sp-shift-identification, part 3; Stacks Tag 05TC (1)
(blueprint: lem-sp-shift-identification).

Proof: (6) The single complex `X[0]`, where `X = H^q(K)`, has no negative cohomology.
By lem-weil-pbc-derived-functor-negative-vanishing with lower bound zero, `H^p(RF(X[0]))`
is zero. Part 1 transports this to `H^(p+q)(RF(X[0][-q]))`; alternatively use lower bound
`q` on `X[0][-q]` and `p+q < q`. The middle term is the same cohomology object of `RF(X[0])`.
The ordinary derived functor in negative degree is zero by the stated convention. -/
theorem isZero_rightDerived_shift_identification [PreservesFiniteLimits F]
    (K : CochainComplex.Plus C)
    (p q : ℤ) (hp : p < 0) :
    let X := K.obj.homology q
    let L := (DerivedCategory.Plus.singleFunctor C 0).obj X
    let RF := F.rightDerivedFunctorPlus
    IsZero ((DerivedCategory.Plus.homologyFunctor D (p + q)).obj (RF.obj (L⟦-q⟧))) ∧
      IsZero ((DerivedCategory.Plus.homologyFunctor D p).obj (RF.obj L)) ∧
      IsZero (if p < 0 then (0 : D) else (F.rightDerived p.toNat).obj X) := by
  dsimp only
  let X := K.obj.homology q
  let L := (DerivedCategory.Plus.singleFunctor C 0).obj X
  let RF := F.rightDerivedFunctorPlus
  have h : IsZero ((DerivedCategory.Plus.homologyFunctor D p).obj (RF.obj L)) :=
    F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE L 0 hp
  refine ⟨?_, h, ?_⟩
  · exact IsZero.of_iso h
      ((DerivedCategory.Plus.homologyFunctor D (p + q)).mapIso
        ((RF.commShiftIso (-q)).app L) ≪≫
        ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso (-q) (p + q) p
          (by omega)).app (RF.obj L))
  · simpa only [ite_eq_left hp] using (isZero_zero D)

end CategoryTheory.Functor
