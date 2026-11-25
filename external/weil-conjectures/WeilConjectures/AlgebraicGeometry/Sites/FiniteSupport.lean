/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyBijective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Étale sheaves supported on finitely many closed points

An abelian étale sheaf on a geometric point `Spec k`, `k` separably closed, has no cohomology in
positive degrees: the constant sheaf `ℤ` is projective. Consequently, a sheaf on a scheme `X`
which vanishes off a finite set `S` of closed points with separably closed residue fields is
acyclic: it is the direct sum of the direct images of its restrictions to the points of `S`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`: `Hⁿ(Spec k, H) = 0` for `n ≥ 1`.
- `AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar`: a sheaf whose restriction to the
  complement of a finite set of closed points with separably closed residue fields vanishes has
  no cohomology in positive degrees.
- `AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map`: a morphism of sheaves which
  is an isomorphism away from such a finite set induces bijections in degrees at least two.
- `AlgebraicGeometry.Etale.isIso_upperStar_map_unit_of_isUniversalHomeomorphism`: the unit
  `F ⟶ ν_* ν^* F` of a finite morphism `ν` is an isomorphism over every open over which `ν` is a
  universal homeomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

/-- **Cohomology of a geometric point.**

Over a separably closed field `k` every abelian étale sheaf on `Spec k` has no cohomology in
positive degrees. -/
theorem Scheme.subsingleton_H_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (H : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Subsingleton (Sheaf.H H (n + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

namespace Etale

open Scheme

variable {X : Scheme.{u}}

/-- **Sheaves supported on finitely many closed points are acyclic.** Let `U` be an open subset
of a scheme `X` whose complement is a finite set of closed points with separably closed residue
fields, and `G` an abelian étale sheaf on `X` whose restriction to `U` vanishes. Then
`Hⁿ(X, G) = 0` for `n ≥ 1`. -/
theorem subsingleton_H_of_isZero_upperStar (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (hsep : ∀ x ∉ U, IsSepClosed (X.residueField x))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsZero ((U.ι)^*[AddCommGrpCat.{u + 1}].obj G)) (n : ℕ) :
    Subsingleton (Sheaf.H G (n + 1)) := by
  let ι := {x : X // x ∉ U}
  have : Finite ι := hfin.to_subtype
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (x : ι) : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x.1 x.2)
  let adj (x : ι) := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (X.fromSpecResidueField x.1)
  let G' (x : ι) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (X.fromSpecResidueField x.1)_*[AddCommGrpCat.{u + 1}].obj
      ((X.fromSpecResidueField x.1)^*[AddCommGrpCat.{u + 1}].obj G)
  let φ : G ⟶ ⨁ G' := biproduct.lift fun x ↦ (adj x).unit.app G
  -- each `G' x` has no cohomology in positive degrees
  have hG' (x : ι) : Subsingleton (Sheaf.H (G' x) (n + 1)) :=
    have := hsep x.1 x.2
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (Spec (X.residueField x.1)).smallEtaleTopology
      AddCommGrpCat.{u + 1})).obj ((X.fromSpecResidueField x.1)^*[AddCommGrpCat.{u + 1}].obj G))
        (n + 1)) := subsingleton_H_of_isSepClosed (X.residueField x.1) _ n
    (bijective_edgeMap_of_isFinite (X.fromSpecResidueField x.1) _ (n + 1)).injective.subsingleton
  -- the family consisting of `U` and of the points `x ∉ U` is jointly surjective
  let V : Option ι → Scheme.{u} := fun o ↦ o.elim (U : Scheme.{u})
    fun x ↦ Spec (X.residueField x.1)
  let a : ∀ o, V o ⟶ X := fun o ↦ match o with
    | none => U.ι
    | some x => X.fromSpecResidueField x.1
  have hφ : IsIso φ := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1} a
      (fun y ↦ ?_) φ fun o ↦ ?_
    · by_cases hy : y ∈ U
      · exact ⟨none, ⟨y, hy⟩, rfl⟩
      · exact ⟨some ⟨y, hy⟩, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩
    rcases o with _ | x
    · let P := (U.ι)^*[AddCommGrpCat.{u + 1}]
      have hz (x : ι) : IsZero (P.obj (G' x)) :=
        isZero_upperStar_lowerStar_of_disjoint_range _ U.ι (X.fromSpecResidueField x.1)
          (by
            rw [Scheme.range_fromSpecResidueField, Set.disjoint_singleton_right]
            simpa using x.2) _
      have : IsZero (P.obj (⨁ G')) := by
        rw [IsZero.iff_id_eq_zero, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'),
          P.map_sum]
        exact Finset.sum_eq_zero fun j _ ↦ by
          rw [P.map_comp, (hz j).eq_of_tgt (P.map (biproduct.π G' j)) 0, zero_comp]
      exact (hG.eq_of_src (P.map φ) (hG.iso this).hom) ▸ Iso.isIso_hom _
    · let P := (X.fromSpecResidueField x.1)^*[AddCommGrpCat.{u + 1}]
      have hz (y : ι) (hxy : y ≠ x) : IsZero (P.obj (G' y)) := by
        -- `iₓ` factors through the open complement `V` of `y`, over which `G' y` vanishes
        let V : X.Opens := ⟨{y.1}ᶜ, (hcl y.1 y.2).isOpen_compl⟩
        have hV : Set.range (X.fromSpecResidueField x.1) ⊆ Set.range V.ι := by
          rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
          exact fun h ↦ hxy (Subtype.ext h).symm
        have h0 := isZero_upperStar_lowerStar_of_disjoint_range _ V.ι (X.fromSpecResidueField y.1)
          (by rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]; simp [V])
          ((X.fromSpecResidueField y.1)^*[AddCommGrpCat.{u + 1}].obj G)
        exact (Functor.map_isZero (IsOpenImmersion.lift V.ι _ hV)^*[AddCommGrpCat.{u + 1}]
          h0).of_iso ((upperStarComp AddCommGrpCat.{u + 1} (IsOpenImmersion.lift V.ι _ hV)
            V.ι _ (IsOpenImmersion.lift_fac _ _ _).symm).app _)
      have hπ : IsIso (P.map (biproduct.π G' x)) := by
        refine ⟨P.map (biproduct.ι G' x), ?_, ?_⟩
        · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'), P.map_sum,
            Finset.sum_eq_single x (fun y _ hxy ↦ ?_) (by simp)]
          rw [P.map_comp, (hz y hxy).eq_zero_of_tgt (P.map (biproduct.π G' y)), zero_comp]
        · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
      have hunit : IsIso (P.map ((adj x).unit.app G)) := by
        have : IsIso (P.map ((adj x).unit.app G) ≫ (adj x).counit.app (P.obj G)) := by
          rw [(adj x).left_triangle_components G]
          exact IsIso.id _
        exact IsIso.of_isIso_comp_right _ ((adj x).counit.app (P.obj G))
      have : IsIso (P.map φ ≫ P.map (biproduct.π G' x)) := by
        rw [← P.map_comp, biproduct.lift_π]
        exact hunit
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  have : Subsingleton (Sheaf.H (⨁ G') (n + 1)) :=
    have : ∀ x, Subsingleton (Sheaf.H (G' x) (n + 1)) := hG'
    (Ext.addEquivBiproduct _ (biproduct.isBilimit G') (n + 1)).toEquiv.subsingleton
  refine (Function.LeftInverse.injective (f := Sheaf.H.map φ (n + 1))
    (g := Sheaf.H.map (inv φ) (n + 1)) fun x ↦ ?_).subsingleton
  rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]

/-- **Isomorphisms away from finitely many closed points.** Let `U` be an open subset of a
scheme `X` whose complement is a finite set of closed points with separably closed residue
fields, and `φ : F ⟶ G` a morphism of abelian étale sheaves on `X` which is an isomorphism over
`U`. Then `Hⁿ(X, F) → Hⁿ(X, G)` is bijective for `n ≥ 2`. -/
theorem bijective_H_map_of_isIso_upperStar_map (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (hsep : ∀ x ∉ U, IsSepClosed (X.residueField x))
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (hφ : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map φ)) (n : ℕ) :
    Function.Bijective (Sheaf.H.map φ (n + 2)) := by
  let P := (U.ι)^*[AddCommGrpCat.{u + 1}]
  refine Sheaf.H.bijective_map_of_subsingleton φ (fun i ↦ ?_) (fun i ↦ ?_) n
  · refine subsingleton_H_of_isZero_upperStar U hfin hcl hsep _ ?_ i
    exact (isZero_kernel_of_mono (P.map φ)).of_iso (PreservesKernel.iso P φ)
  · refine subsingleton_H_of_isZero_upperStar U hfin hcl hsep _ ?_ i
    exact (isZero_cokernel_of_epi (P.map φ)).of_iso (PreservesCokernel.iso P φ)

/-- Let `ν : Y ⟶ X` be finite and `U` an open subset of `X` over which `ν` is a universal
homeomorphism. Then the unit `F ⟶ ν_* ν^* F` is an isomorphism over `U`. -/
theorem isIso_upperStar_map_unit_of_isUniversalHomeomorphism {Y : Scheme.{u}} (ν : Y ⟶ X)
    [IsFinite ν] (U : X.Opens) [IsUniversalHomeomorphism (ν ∣_ U)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ν).unit.app F)) := by
  have sq := (isPullback_morphismRestrict ν U).flip
  have hBC := Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
  have := isEquivalence_upperStar AddCommGrpCat.{u + 1} (ν ∣_ U)
  have key := map_unit_baseChangeMap_app AddCommGrpCat.{u + 1} sq.toCommSq F
  have : IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ν ∣_ U)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ν).unit.app F) ≫
        (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((ν)^*[AddCommGrpCat.{u + 1}].obj F)) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app ((ν)^*[AddCommGrpCat.{u + 1}].obj F))

end Etale

end AlgebraicGeometry
