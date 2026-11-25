/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # The bottom derived unit on a lower-truncated complex

Source: Stacks Project, Tag 05TC (2) and the single-object calculation of
Tags 015A, 05TH and 05TI.
(blueprint: lem-sc-derived-lower-truncation-unit-bridge).
-/

@[expose] public section

universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Localization identifies good lower truncation with t-structure lower truncation,
with the canonical projection fixed.

Source: Stacks Project, Derived Categories, Tag 015A; uniqueness of truncation
triangles, as in the parent bridge step 1.

Proof: The good truncation short exact sequence at n - 1 gives a distinguished
triangle in the derived category. Its first term has homology only below n and
its third term is Q(truncGE n I), which has no homology below n. The universal
property of truncation therefore gives the unique isomorphism from this third
term to tauGE n QI commuting with the projection out of QI. Compose on the
source with quotientCompQhIso at truncGE n I. Naturality of quotientCompQhIso
identifies the projection from Qh(PI) with the image of I.πTruncGE n. This proves
the stated equality. The construction works for every integer n and any
unbounded I; when I is zero the unique isomorphism is the zero-object one. -/
private theorem lowerTruncationLocalization
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (I : CochainComplex C ℤ) (n : ℤ) :
    ∃ e : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj (I.truncGE n)) ≅
        (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I),
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
          (I.πTruncGE n)) ≫ e.hom =
        (DerivedCategory.quotientCompQhIso C).hom.app I ≫
          (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let p := DerivedCategory.Q.map (I.πTruncGE n)
  let b := t.descTruncGE p n
  have hb : (t.truncGEπ n).app (DerivedCategory.Q.obj I) ≫ b = p :=
    t.π_descTruncGE p n
  have hi : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := DerivedCategory.homologyFunctor C i
    by_cases h : n ≤ i
    · have : IsIso (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ n i h
      have : QuasiIsoAt (I.πTruncGE n) i :=
        I.quasiIsoAt_πTruncGE n i h
      have hp : IsIso (H.map p) := by
        change IsIso ((DerivedCategory.Q ⋙ H).map (I.πTruncGE n))
        rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i)]
        change IsIso (HomologicalComplex.homologyMap (I.πTruncGE n) i)
        infer_instance
      have : IsIso (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I)) ≫
          H.map b) := by
        rw [← H.map_comp, hb]
        exact hp
      exact IsIso.of_isIso_comp_left
        (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I))) (H.map b)
    · have h' : i < n := by omega
      exact isIso_of_source_target_iso_zero (H.map b)
        (DerivedCategory.isZero_of_isGE _ n i h').isoZero
        (DerivedCategory.isZero_of_isGE _ n i h').isoZero
  let a := (DerivedCategory.quotientCompQhIso C).app (I.truncGE n) ≪≫ (asIso b).symm
  refine ⟨a, ?_⟩
  dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc]
  erw [(DerivedCategory.quotientCompQhIso C).hom.naturality (I.πTruncGE n)]
  change ((DerivedCategory.quotientCompQhIso C).hom.app I ≫ p) ≫ inv b = _
  rw [← hb]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl


private theorem preservesBottomHomology
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    F.PreservesLeftHomologyOf (K.sc n) := by
  refine ⟨fun h ↦ ?_⟩
  have hf : (K.sc n).f = 0 := by
    change K.d ((ComplexShape.up ℤ).prev n) n = 0
    exact (K.isZero_of_isStrictlyGE n _ (by simp)).eq_of_src _ _
  have hf' : h.f' = 0 := by
    rw [← cancel_mono h.i, ShortComplex.LeftHomologyData.f'_i, zero_comp]
    exact hf
  exact { g := inferInstance, f' := preservesCokernel_zero' F _ hf' }

set_option backward.isDefEq.respectTransparency false in
/-- The actual right-derived unit is invertible on bottom cohomology of a
complex that is strictly zero in lower degrees.

Source: Stacks Project, Derived Categories, Tags 05TC (2), 05TH, 05TI, 015A;
parent bridge step 2.

Proof: Choose a quasi-isomorphism K → L with L injective termwise and strictly
zero below the same n. Such L is K-injective, so its derived unit is invertible.
Both K and L have zero incoming differential in degree n. Their bottom homology
is a kernel, preserved by F; naturality of the preserved homology comparison
therefore makes H^n(F(K → L)) invertible. Localization makes Qh(P(K → L))
invertible as well. Naturality of the actual derived unit gives its bottom
homology map at K as a composite of these isomorphisms. No shifts or
bounded-below/unbounded comparison is required; arbitrary integer n and zero
complexes obey the same argument. -/
private theorem isIsoBottomUnit
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))) := by
  let P := HomotopyCategory.quotient C (.up ℤ)
  let M := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor D n
  obtain ⟨L, i, hi, hL, hn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  let := hi
  let := hn
  let (j : ℤ) : Injective (L.X j) := hL j
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L n
  let := preservesBottomHomology F K n
  let := preservesBottomHomology F L n
  let φ := (HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map i
  have hmap : IsIso (HomologicalComplex.homologyMap (M.map i) n) := by
    have hnat := ShortComplex.mapHomologyIso_hom_naturality φ F
    have hφ : IsIso (ShortComplex.homologyMap φ) :=
      inferInstanceAs (IsIso (HomologicalComplex.homologyMap i n))
    have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
        ((L.sc n).mapHomologyIso F).hom) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (ShortComplex.homologyMap (F.mapShortComplex.map φ)) ((L.sc n).mapHomologyIso F).hom
  have hQ : IsIso (DerivedCategory.Qh.map (P.map i)) := by
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
      (P.map i) (by simpa [P, HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff] using hi)
  have hFM : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (P.map i)))) := by
    rw [Functor.mapHomotopyCategory_map]
    erw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh D n)]
    erw [NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors D (.up ℤ) n)]
    exact hmap
  have hnat := F.rightDerivedFunctorUnit.naturality (P.map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (H.map (F.rightDerivedFunctorUnit.app (P.obj K)) ≫
      H.map (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (P.map i)))) := by
    rw [← H.map_comp, ← hnat, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (F.rightDerivedFunctorUnit.app (P.obj K)))
    (H.map (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (P.map i))))


set_option backward.isDefEq.respectTransparency false in
/-- The derived edge map factors through the underived lower truncation, and
its bottom-degree comparison there is invertible. This concerns the derived
unit and localization only; it contains no cycle-class or homology quotient map.

Source: Stacks Project, Tag 05TC (2); Tags 015A, 05TH, 05TI, and naturality of
localization and of the right-derived unit.
(blueprint: lem-sc-derived-lower-truncation-unit-bridge).

Proof: Put K = truncGE n I. In the derived category, QK is the good lower
truncation of QI: the short exact truncation sequence gives a distinguished
triangle whose first object is strictly below n and whose last object is at
least n. Uniqueness of the truncation triangle gives a canonical isomorphism
QK to tauGE n QI, commuting with the projection from QI. Compose its inverse
with the quotient-to-homotopy factor isomorphism to identify Q_h(PK) with
this lower truncation.

The derived unit at K is an isomorphism on H^n. To see this with the actual
unit, upper-truncate K at n. Negative vanishing (Tag 05TC) makes the derived
upper-truncation inclusion invertible on H^n. Double truncation is H^n(K)
placed in degree n. Shift it to degree zero. The derived unit on a single
object is the canonical F to R^0 F map, computed by the augmentation of an
injective resolution. F preserves the augmentation kernel, so this map is
invertible. Naturality of the unit for the upper-truncation inclusion and
the double-truncation projection transports invertibility back to K. No
choice of an arbitrary bottom cohomology isomorphism is involved.

Define d by the inverse homotopy and derived homology factor isomorphisms
for F(K), followed by H^n of the unit at K and by H^n of RF of the canonical
isomorphism Q_h(PK) to tauGE n QI. Each factor is invertible, hence so is d.
Naturality of the unit at P(I to K), naturality of the homology factor
isomorphisms, and the commuting truncation-projection triangle identify
e H^n(U) H^n(q) with H^n(F(I to K)) d. The argument only uses that K is
strictly zero below n, so all integers n, unbounded I, and zero complexes
satisfy the same calculation. -/
theorem derived_lower_truncation_unit_bridge
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let H := DerivedCategory.homologyFunctor D n
    let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh D n).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
    let U := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)
    let q := F.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso C).hom.app I ≫
        (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))
    ∃ d : ((F.mapHomologicalComplex (.up ℤ)).obj (I.truncGE n)).homology n ≅
        H.obj (F.rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I))),
      e.hom ≫ H.map U ≫ H.map q =
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (I.πTruncGE n)) n ≫ d.hom := by
  dsimp only
  let P := HomotopyCategory.quotient C (.up ℤ)
  let PD := HomotopyCategory.quotient D (.up ℤ)
  let M := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor D n
  let K := I.truncGE n
  let f := I.πTruncGE n
  obtain ⟨a, ha⟩ := lowerTruncationLocalization I n
  have hu := isIsoBottomUnit F K n
  let eK := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app
      (M.obj K)).symm ≪≫
    ((DerivedCategory.homologyFunctorFactorsh D n).app (PD.obj (M.obj K))).symm
  refine ⟨eK ≪≫ asIso (H.map (F.rightDerivedFunctorUnit.app (P.obj K))) ≪≫
    H.mapIso (F.rightDerivedFunctor.mapIso a), ?_⟩
  have hn := F.rightDerivedFunctorUnit.naturality (P.map f)
  dsimp only [Functor.comp_map] at hn
  have he :
      (((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app
          (M.obj I)).symm ≪≫
        ((DerivedCategory.homologyFunctorFactorsh D n).app (PD.obj (M.obj I))).symm).hom ≫
        H.map (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (P.map f))) =
      HomologicalComplex.homologyMap (M.map f) n ≫ eK.hom := by
    rw [Functor.mapHomotopyCategory_map]
    dsimp only [Iso.trans_hom, Iso.symm_hom, eK]
    simp only [Category.assoc]
    erw [← (DerivedCategory.homologyFunctorFactorsh D n).inv.naturality
      (PD.map (M.map f))]
    erw [← (HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).inv.naturality_assoc
      (M.map f)]
    rfl
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  rw [← ha, F.rightDerivedFunctor.map_comp, H.map_comp]
  rw [← H.map_comp_assoc, ← hn, H.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom] at he
  simp only [Category.assoc, Iso.symm_hom]
  rw [reassoc_of% he]

end AlgebraicGeometry
