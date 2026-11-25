/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import WeilConjectures.AlgebraicGeometry.PerfectCommonAffineModels
import WeilConjectures.AlgebraicGeometry.StrictPerfectTensorLocalComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.Data.Int.Interval

/-! # Derived tensor products of perfect complexes

Source: literature/stacks-project/cohomology.tex, Lemma 09J5
(blueprint: lem-sc-perfect-derived-tensor-perfect).
-/

@[expose] public section

universe uT wT

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private local instance pdt_localTensorZero (X : Scheme.{uT}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private local instance pdt_localTensorObjZero (X : Scheme.{uT}) (U : X.Opens)
    (M : SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private local instance pdt_localTotal (X : Scheme.{uT}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Total tensor of strictly perfect complexes is strictly perfect (Stacks, Tag 09J5). -/
private theorem strictlyPerfect_totalTensor (X : Scheme.{uT}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : Scheme.IsStrictlyPerfect X U A) (hB : Scheme.IsStrictlyPerfect X U B) :
    Scheme.IsStrictlyPerfect X U (CochainComplex.mapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U)))) := by
  classical
  let : MonoidalCategory
      (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  have : HasFiniteBiproducts
      (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨⟨a, b, hAb⟩, hAf⟩ := hA
  obtain ⟨⟨c, d, hBb⟩, hBf⟩ := hB
  constructor
  · refine ⟨a + c, b + d, fun n hn ↦ ?_⟩
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    have hz : IsZero (A.X p ⊗ B.X q) := by
      by_cases hp : p < a ∨ b < p
      · exact (tensorRight (B.X q)).map_isZero (hAb p hp)
      · exact (tensorLeft (A.X p)).map_isZero (hBb q (by omega))
    exact hz.eq_of_src _ _
  · intro n
    choose m ia ra hia using hAf
    choose k ib rb hib using hBf
    let J := {pq : ℤ × ℤ // pq.1 + pq.2 = n ∧ pq.1 ∈ Finset.Icc a b}
    have : Finite J := Finite.of_injective
      (fun j : J ↦ (⟨j.1.1, j.2.2⟩ : ↥(Finset.Icc a b))) (by
        intro j l h
        apply Subtype.ext
        have hp : j.1.1 = l.1.1 := congrArg Subtype.val h
        apply Prod.ext hp
        have hj := j.2.1
        have hl := l.2.1
        omega)
    let : Fintype J := Fintype.ofFinite J
    let I (j : J) := Σ _ : ULift.{uT} (Fin (m j.1.1)), ULift.{uT} (Fin (k j.1.2))
    let R := (moduleRings X.toRingedSpace).over U
    let F (j : J) := A.X j.1.1 ⊗ B.X j.1.2
    let G (j : J) := SheafOfModules.free (R := R) (I j)
    let e (j : J) :
        (SheafOfModules.free (R := R) (ULift.{uT} (Fin (m j.1.1))) ⊗
          SheafOfModules.free (R := R) (ULift.{uT} (Fin (k j.1.2)))) ≅ G j :=
      SheafOfModules.freeTensorFreeIso (R := X.sheaf.over U) _ _
    let i (j : J) : F j ⟶ G j := (ia j.1.1 ⊗ₘ ib j.1.2) ≫ (e j).hom
    let r (j : J) : G j ⟶ F j := (e j).inv ≫ (ra j.1.1 ⊗ₘ rb j.1.2)
    have hir (j : J) : i j ≫ r j = 𝟙 (F j) := by
      simp only [i, r, Category.assoc, Iso.hom_inv_id_assoc,
        tensorHom_comp_tensorHom, hia, hib, tensorHom_id, id_whiskerRight]
      rfl
    let eFree : (⨁ G) ≅ SheafOfModules.free (R := R)
        (ULift.{uT} (Fin (Fintype.card (Σ j : J, I j)))) :=
      biproduct.isoCoproduct G ≪≫
        sigmaSigmaIso I (fun _ _ ↦ SheafOfModules.unit R) ≪≫
        (SheafOfModules.freeFunctor (R := R)).mapIso
          ((Fintype.equivFin (Σ j : J, I j)).trans Equiv.ulift.symm).toIso
    let backMap : (⨁ F) ⟶ (CochainComplex.mapBifunctor A B (curriedTensor _)).X n :=
      biproduct.desc (fun j ↦ HomologicalComplex.ιMapBifunctor A B (curriedTensor _)
        (ComplexShape.up ℤ) j.1.1 j.1.2 n j.2.1)
    let forwardMap : (CochainComplex.mapBifunctor A B (curriedTensor _)).X n ⟶ (⨁ F) :=
      HomologicalComplex.mapBifunctorDesc
        (K₁ := A) (K₂ := B) (F := curriedTensor _) (c := ComplexShape.up ℤ)
        (fun p q h ↦ if hp : p ∈ Finset.Icc a b then
          biproduct.ι F ⟨(p, q), ⟨h, hp⟩⟩ else 0)
    have hfb : forwardMap ≫ backMap = 𝟙 _ := by
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      dsimp only [forwardMap, backMap]
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      by_cases hp : p ∈ Finset.Icc a b
      · simp only [dite_eq_left hp, biproduct.ι_desc, Category.comp_id]
      · rw [dite_eq_right hp, zero_comp]
        have hz : IsZero (A.X p ⊗ B.X q) :=
          (tensorRight (B.X q)).map_isZero (hAb p (by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hp
            exact hp))
        exact hz.eq_of_src _ _
    have hsum : biproduct.map i ≫ biproduct.map r = 𝟙 _ := by
      apply biproduct.hom_ext
      intro j
      rw [Category.assoc, biproduct.map_π, ← Category.assoc, biproduct.map_π,
        Category.assoc, hir, Category.comp_id, Category.id_comp]
    refine ⟨_, forwardMap ≫ biproduct.map i ≫ eFree.hom,
      eFree.inv ≫ biproduct.map r ≫ backMap, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (biproduct.map i), hsum, Category.id_comp, hfb]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 256 in
/-- (blueprint: lem-sc-perfect-derived-tensor-perfect) If `K, L` are perfect objects of
`D(𝒪_X)`, then so is `K ⊗^L_{𝒪_X} L`.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09J5.

The conclusion is expressed through K-flat representatives, as in
def-pc-derived-tensor-cohomology-vanishes, lem-pc-derived-pullback-tensor-qcoh and
lem-pc-derived-pullback-tensor-product, `K ⊗^L L` is stated through K-flat representatives:
for K-flat complexes `P, N` of `𝒪_X`-modules with `Q(P) ≅ K` and `Q(N) ≅ L`,
`K ⊗^L L ≅ Q(Tot(P ⊗_{𝒪_X} N))` (tensor `SheafOfModules.monoidalCategory X.sheaf`,
def-pc-tensor-complex-sheaves). K-flat resolutions exist (lem-pc-kflat-resolution), so
quantifying over all such `P, N` covers every pair `K, L`.

Proof (Stacks 09J5): perfectness is local. Given `x`, choose opens around `x` on which `K`
and `L` are isomorphic to strictly perfect complexes and intersect them to `U`. Restriction to
`U` commutes with the representative tensor, and on `U` the derived tensor is computed by the
strictly perfect (bounded, termwise finite projective, hence K-flat) models; their total
tensor complex is bounded with terms direct summands of finite free `𝒪_U`-modules, i.e.
strictly perfect. Hence `Q(Tot(P ⊗ N))` is perfect by the definition of `IsPerfect`. -/
theorem perfect_derivedTensor (X : Scheme.{uT})
    [HasDerivedCategory.{wT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wT}
        (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hK : Scheme.IsPerfect X K) (hL : Scheme.IsPerfect X L)
    (P N : CochainComplex (SheafOfModules.{uT} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N)
    (eP : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj N ≅ L) :
    Scheme.IsPerfect X (DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P N
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) := by
  intro x
  obtain ⟨U, hx, _hU, A, B, hA, hB, eA, eB⟩ :=
    Scheme.perfect_common_affine_models X K L hK hL x
  refine ⟨U, hx, CochainComplex.mapBifunctor A B
    (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))),
    strictlyPerfect_totalTensor X U A B hA hB, ?_⟩
  exact strictPerfect_tensor_localComparison X U P N hP hN A B hA hB
    ⟨(SheafOfModules.overFunctor.{uT}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso eP ≪≫ eA.some⟩
    ⟨(SheafOfModules.overFunctor.{uT}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso eN ≪≫ eB.some⟩

end AlgebraicGeometry
