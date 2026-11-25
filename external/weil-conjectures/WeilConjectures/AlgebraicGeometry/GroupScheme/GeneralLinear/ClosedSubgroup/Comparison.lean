/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Product

/-!
# The group–Lie comparison for closed subgroup schemes of `GL_n`

This file reads the matrix results of
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.LieSubalgebra` on the
Lie algebra `Lie(G)` of a closed subgroup scheme `G = V(I)` of `GL_n`, in the sense of
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`.

A tangent vector `x ∈ Lie(G)` is an infinitesimal point of `G`, that is a point of `G` with values
in the dual numbers `k[ε]` reducing to the identity (`AlgebraicGeometry.GrpObj.tangentPoint`). For
`G = V(I)` its matrix is `1 + εX` with `X` in the matrix Lie algebra `lieSubalgebra I`, and
`x ↦ X` is the differential of the closed immersion `V(I) ⟶ GL_n`: an injective homomorphism of Lie
algebras `Lie(V(I)) → gl_n` with image `lieSubalgebra I`
(`AlgebraicGeometry.GeneralLinearGroup.range_differential_subgroupSchemeι`). The differential of a
rational representation `r` is read on tangent points the same way
(`AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential_eq_map_snd`).

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.range_lieAlgebraMap_center`,
  `AlgebraicGeometry.GeneralLinearGroup.range_lieAlgebraMap_identityComponent_center`: the Lie
  algebra of the centre of a connected `V(I)`, and of its identity component, is the centre of the
  Lie algebra of `V(I)`.

## Blueprint

- `lemma-stable-subspaces-center`: the group–Lie comparison.
- `lemma-stable-subspaces-center--2`: the centre.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry

namespace GeneralLinearGroup

open Matrix.GeneralLinearGroup

/-! ### The Lie algebra of `V(I)` in matrices -/

section ClosedSubgroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

/-- A point of `V(I)` with values in `k[ε]` reducing to the identity is a tangent vector
`1 + εX`. -/
theorem coe_zeroLocusMulEquiv_symm_eq_dualUnit {p : points (subgroupScheme I) (DualNumber k)}
    (hp : p ∈ tangentGroup (subgroupScheme I)) :
    (((zeroLocusMulEquiv I (DualNumber k)).symm p : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)) =
      dualUnit ((((zeroLocusMulEquiv I (DualNumber k)).symm p : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)).map snd) := by
  set M := (zeroLocusMulEquiv I (DualNumber k)).symm p
  have h1 : zeroLocus.map I (fstHom k k k) M = 1 := by
    apply (zeroLocusMulEquiv I k).injective
    rw [zeroLocusMulEquiv_map, MulEquiv.map_one, MulEquiv.apply_symm_apply]
    exact (mem_tangentGroup _).1 hp
  have h2 : ((M : GL n (DualNumber k)) : Matrix n n (DualNumber k)).map fst = 1 :=
    congrArg (fun g : zeroLocus I k ↦ ((g : GL n k) : Matrix n n k)) h1
  rw [coe_dualUnit]
  exact Matrix.eq_one_add_map_inr_of_map_fst_eq_one h2

/-- The point of `V(I)` of a rational representation `ι : V(I) ⟶ GL_n` is its matrix. -/
theorem points_subgroupSchemeι {R : Type u} [CommRing R] [Algebra k R]
    (p : points (subgroupScheme I) R) :
    RationalHom.points (subgroupSchemeι I) R p = ((zeroLocusMulEquiv I R).symm p : GL n R) := by
  rw [RationalHom.points_apply]
  conv_lhs => rw [← (zeroLocusMulEquiv I R).apply_symm_apply p]
  exact homMulEquiv_zeroLocusMulEquiv_comp _

/-- The matrix of the tangent point of a tangent vector `x` of `V(I)` is `1 + εX`, where `X` is the
image of `x` under the differential of the closed immersion `V(I) ⟶ GL_n`. -/
theorem coe_zeroLocusMulEquiv_symm_tangentPoint (x : GrpObj.Lie (subgroupScheme I)) :
    (((zeroLocusMulEquiv I (DualNumber k)).symm (GrpObj.tangentPoint x) : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)) =
      dualUnit (RationalHom.differential (subgroupSchemeι I) x) := by
  rw [RationalHom.differential_eq_map_snd, points_subgroupSchemeι]
  exact coe_zeroLocusMulEquiv_symm_eq_dualUnit (GrpObj.tangentPoint_mem_tangentGroup x)

theorem dualUnit_differential_subgroupSchemeι (x : GrpObj.Lie (subgroupScheme I)) :
    dualUnit (RationalHom.differential (subgroupSchemeι I) x) =
      ((zeroLocusMulEquiv I (DualNumber k)).symm (GrpObj.tangentPoint x) : GL n (DualNumber k)) :=
  Units.ext (coe_zeroLocusMulEquiv_symm_tangentPoint x).symm

/-- The differential of the closed immersion `V(I) ⟶ GL_n` takes values in the matrix Lie algebra
of `V(I)`. -/
theorem differential_subgroupSchemeι_mem (x : GrpObj.Lie (subgroupScheme I)) :
    RationalHom.differential (subgroupSchemeι I) x ∈ lieSubalgebra I := by
  rw [mem_lieSubalgebra, dualUnit_differential_subgroupSchemeι]
  exact SetLike.coe_mem _

theorem dualUnit_injective {R : Type*} [CommRing R] :
    Function.Injective (dualUnit : Matrix n n R → GL n (DualNumber R)) := fun X Y h ↦ by
  have := congrArg (fun g : GL n (DualNumber R) ↦ ((g : Matrix n n (DualNumber R))).map snd) h
  simpa [coe_dualUnit, Matrix.map_add, Matrix.one_apply, apply_ite snd] using this

/-- The differential of the closed immersion `V(I) ⟶ GL_n` is injective. -/
theorem differential_subgroupSchemeι_injective :
    Function.Injective (RationalHom.differential (subgroupSchemeι I)) := fun x y h ↦ by
  have h' := congrArg dualUnit h
  rw [dualUnit_differential_subgroupSchemeι, dualUnit_differential_subgroupSchemeι] at h'
  exact GrpObj.tangentPoint_injective
    ((zeroLocusMulEquiv I _).symm.injective (Subtype.ext h'))

/-- Every matrix of the Lie algebra of `V(I)` is the differential of a tangent vector. -/
theorem exists_differential_subgroupSchemeι_eq {X : Matrix n n k} (hX : X ∈ lieSubalgebra I) :
    ∃ x : GrpObj.Lie (subgroupScheme I), RationalHom.differential (subgroupSchemeι I) x = X := by
  set p := zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit X, hX⟩
  have hp : p ∈ tangentGroup (subgroupScheme I) := by
    rw [mem_tangentGroup, points.map, ← zeroLocusMulEquiv_map]
    convert (zeroLocusMulEquiv I k).map_one
    exact Subtype.ext (map_fstHom_dualUnit X)
  obtain ⟨x, hx⟩ := GrpObj.exists_tangentPoint_eq hp
  refine ⟨x, dualUnit_injective ?_⟩
  rw [dualUnit_differential_subgroupSchemeι, hx, MulEquiv.symm_apply_apply]

/-- The differentials of the closed immersions `V(J) ⟶ V(I) ⟶ GL_n` and `V(J) ⟶ GL_n` agree. -/
theorem differential_subgroupSchemeι_lieAlgebraMap {J : Ideal (CoordinateRing n k)}
    [J.IsHopfIdeal k] (h : I ≤ J) (x : GrpObj.Lie (subgroupScheme J)) :
    RationalHom.differential (subgroupSchemeι I) (lieAlgebraMap h x) =
      RationalHom.differential (subgroupSchemeι J) x := by
  rw [RationalHom.differential_eq_map_snd, RationalHom.differential_eq_map_snd,
    GrpObj.tangentPoint_differential, RationalHom.points_apply, RationalHom.points_apply,
    Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι]

/-- A tangent vector of `V(I)` is tangent to `V(J) ⊆ V(I)` if and only if its matrix lies in the
Lie algebra of `V(J)`. -/
theorem mem_range_lieAlgebraMap_iff {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k]
    (h : I ≤ J) {x : GrpObj.Lie (subgroupScheme I)} :
    x ∈ (lieAlgebraMap h).range ↔
      RationalHom.differential (subgroupSchemeι I) x ∈ lieSubalgebra J := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    change RationalHom.differential (subgroupSchemeι I) (lieAlgebraMap h y) ∈ _
    rw [differential_subgroupSchemeι_lieAlgebraMap]
    exact differential_subgroupSchemeι_mem y
  · obtain ⟨y, hy⟩ := exists_differential_subgroupSchemeι_eq hx
    refine ⟨y, differential_subgroupSchemeι_injective ?_⟩
    change RationalHom.differential (subgroupSchemeι I) (lieAlgebraMap h y) = _
    rw [differential_subgroupSchemeι_lieAlgebraMap, hy]

/-- A tangent vector `x` of `V(I)` is central in `Lie(V(I))` if and only if its matrix commutes
with the matrix Lie algebra of `V(I)`. -/
theorem mem_center_iff_commute {x : GrpObj.Lie (subgroupScheme I)} :
    x ∈ LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) ↔
      ∀ Y ∈ lieSubalgebra I, Y * RationalHom.differential (subgroupSchemeι I) x =
        RationalHom.differential (subgroupSchemeι I) x * Y := by
  set d := RationalHom.differential (subgroupSchemeι I)
  rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
  constructor
  · intro h Y hY
    obtain ⟨y, rfl⟩ := exists_differential_subgroupSchemeι_eq hY
    have := congrArg d (h y)
    rwa [LieHom.map_lie, map_zero, Ring.lie_def, sub_eq_zero] at this
  · intro h y
    refine differential_subgroupSchemeι_injective ?_
    rw [LieHom.map_lie, map_zero, Ring.lie_def, sub_eq_zero]
    exact h _ (differential_subgroupSchemeι_mem y)

/-- The Lie algebra of the reduced centre of a reduced `G = V(I)` over an algebraically closed
field is contained in the centre of the Lie algebra of `G`: its tangent vectors commute with
`G(k)`, hence with `Lie G` (`commute_of_mem_lieSubalgebra_center`). (blueprint:
`lemma-stable-subspaces-center`)
-/
theorem range_lieAlgebraMap_center_le [IsAlgClosed k] (hI : I.IsRadical) :
    (lieAlgebraMap (le_center I)).range ≤
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) := by
  intro x hx
  change x ∈ LieAlgebra.center k _
  rw [mem_center_iff_commute]
  intro Y hY
  exact (commute_of_mem_lieSubalgebra_center hI ((mem_range_lieAlgebraMap_iff _).1 hx) hY).symm

/-- In characteristic zero, the centre of the Lie algebra of a connected group `G = V(I)` is
contained in the Lie algebra of the reduced centre `V(center I)`: a matrix commuting with `Lie G`
commutes with the connected `G(k)` (`mem_lieSubalgebra_center_iff`). (blueprint:
`lemma-stable-subspaces-center`)
-/
theorem le_range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) ≤
      (lieAlgebraMap (le_center I)).range := by
  have := hconn.isPrime
  intro x hx
  change x ∈ LieAlgebra.center k _ at hx
  rw [mem_center_iff_commute] at hx
  rw [mem_range_lieAlgebraMap_iff, mem_lieSubalgebra_center_iff]
  exact ⟨differential_subgroupSchemeι_mem x, fun Y hY ↦ (hx Y hY).symm⟩

/-- The group–Lie comparison for the centre: over an algebraically closed field of characteristic
zero, the Lie algebra of the centre of a connected algebraic group is the centre of its Lie
algebra. (blueprint: `lemma-stable-subspaces-center`, `lemma-stable-subspaces-center--2`) -/
theorem range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    (lieAlgebraMap (le_center I)).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) :=
  le_antisymm (range_lieAlgebraMap_center_le hconn.isRadical) (le_range_lieAlgebraMap_center hconn)

/-- The Lie algebra of the identity component of the centre of a connected algebraic group is the
centre of its Lie algebra, in characteristic zero: the differential of `Z(G)° ⟶ G` has as range the
centre of `Lie(G)`. In matrices, `Lie Z(G)° = Lie Z(G)` (`lieSubalgebra_identityComponent`).
(blueprint: `lemma-stable-subspaces-center`, `lemma-stable-subspaces-center--2`) -/
theorem range_lieAlgebraMap_identityComponent_center [IsAlgClosed k] [CharZero k]
    (hconn : IsConnected I) :
    (lieAlgebraMap ((le_center I).trans (le_identityComponent (center I)))).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) := by
  rw [← range_lieAlgebraMap_center hconn]
  ext x
  rw [mem_range_lieAlgebraMap_iff, mem_range_lieAlgebraMap_iff, lieSubalgebra_identityComponent]

end ClosedSubgroup

/-! ### Rational representations -/

section Rational

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {m : Type u} [Fintype m] [DecidableEq m]

/-- A rational representation `r` of `V(I)` on `R`-points is evaluation composed with the coordinate
map of `r`: `r(g)(a) = g(r^♯ a)`. -/
theorem RationalHom.evalAlgHom_points_zeroLocusMulEquiv (r : RationalHom (subgroupScheme I) m)
    {R : Type u} [CommRing R] [Algebra k R] (g : zeroLocus I R) [IsMonHom r] :
    evalAlgHom (r.points R (zeroLocusMulEquiv I R g)) =
      (Ideal.Quotient.liftₐ I (evalAlgHom (g : GL n R)) g.2).comp r.coordMap := by
  set χ := Ideal.Quotient.liftₐ I (evalAlgHom (g : GL n R)) g.2
  have hg : zeroLocusMulEquiv I R g = Spec.mapMulEquiv (WithConv.toConv χ) := by
    refine injective_homMulEquiv_comp I R ?_
    dsimp only
    rw [homMulEquiv_zeroLocusMulEquiv_comp, mapMulEquiv_comp_subgroupSchemeι,
      homMulEquiv_mapMulEquiv]
    refine (evalAlgHom_injective (k := k) ?_).symm
    dsimp only
    rw [algHomMulEquiv_apply, WithConv.ofConv_toConv, evalAlgHom_map_genericUnit]
    exact Ideal.Quotient.liftₐ_comp _ _ _
  have hr : Spec.mapMulEquiv (WithConv.toConv χ) ≫ r =
      (Spec.mapMulEquiv (WithConv.toConv (χ.comp r.coordMap)) :
        (Spec (.of R)).asOver (Spec (.of k)) ⟶
          (Spec (.of (CoordinateRing m k))).asOver (Spec (.of k))) := by
    conv_lhs => rw [← r.mapMulEquiv_coordMap]
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [RationalHom.points_apply, hg]
  change evalAlgHom (homMulEquiv m k R (Spec.mapMulEquiv (WithConv.toConv χ) ≫ r)) = _
  rw [hr, homMulEquiv_mapMulEquiv, algHomMulEquiv_apply, WithConv.ofConv_toConv,
    evalAlgHom_map_genericUnit]

/-- A matrix over `k[ε]` reducing to the identity is `1 + ε • X`. -/
theorem eq_one_add_eps_smul_of_map_fst_eq_one {N : Matrix m m (DualNumber k)}
    (hN : N.map fst = 1) :
    N = 1 + (DualNumber.eps : DualNumber k) •
      (algebraMap k (DualNumber k)).mapMatrix (N.map snd) := by
  rw [← coe_dualUnit_eq_one_add_eps_smul, coe_dualUnit]
  exact Matrix.eq_one_add_map_inr_of_map_fst_eq_one hN

/-- The image under a rational representation of a point of `V(I)` reducing to the identity
reduces to the identity. -/
theorem RationalHom.map_fst_points_eq_one (r : RationalHom (subgroupScheme I) m) [IsMonHom r]
    {p : AlgebraicGeometry.points (subgroupScheme I) (DualNumber k)}
    (hp : p ∈ tangentGroup (subgroupScheme I)) :
    ((r.points (DualNumber k) p : GL m (DualNumber k)) : Matrix m m (DualNumber k)).map fst =
      1 := by
  have := congrArg (fun g : GL m k ↦ (g : Matrix m m k)) (r.map_points (fstHom k k k) p)
  rw [(mem_tangentGroup _).1 hp, MonoidHom.map_one, Units.val_one] at this
  refine Matrix.ext fun i j ↦ ?_
  have h := congrFun₂ this i j
  rw [Matrix.GeneralLinearGroup.map_apply] at h
  exact h

end Rational

end GeneralLinearGroup

end AlgebraicGeometry
