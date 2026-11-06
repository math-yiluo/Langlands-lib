import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Reductive.CommutingMultiplication

/-! # Point generation and normality in a commuting product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H K G A : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- The point group of an isomorphic commuting product, in factor coordinates. -/
def commutingProductPointsEquiv
    [IsIso (commutingSubgroupMultiplicationHom j i hc)] (T : Over S) :
    (T ⟶ G.X) ≃* (T ⟶ H.X) × (T ⟶ K.X) := by
  let m := commutingSubgroupMultiplicationHom j i hc
  exact
    { toFun := fun g => productPointsEquiv H K T (g ≫ (inv m).hom.hom)
      invFun := fun x => (productPointsEquiv H K T).symm x ≫ m.hom.hom
      left_inv := fun g => by
        dsimp only
        rw [MulEquiv.symm_apply_apply, Category.assoc, ← Grp.comp_hom_hom,
          IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      right_inv := fun x => by
        dsimp only
        rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.hom_inv_id,
          Grp.id_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply]
      map_mul' := fun g g' => by
        rw [MonObj.mul_comp, map_mul] }

/-- An isomorphic commuting multiplication decomposes points over every test. -/
theorem exists_factor_points_of_isIso_commutingMultiplication
    [IsIso (commutingSubgroupMultiplicationHom j i hc)]
    (T : Over S) (g : T ⟶ G.X) :
    ∃ (h : T ⟶ H.X) (x : T ⟶ K.X),
      (h ≫ j.hom.hom) * (x ≫ i.hom.hom) = g := by
  let m := commutingSubgroupMultiplicationHom j i hc
  have : IsIso m.hom.hom := (Grp.forget (Over S)).map_isIso m
  let y := g ≫ inv m.hom.hom
  refine ⟨y ≫ fst H.X K.X, y ≫ snd H.X K.X, ?_⟩
  change (y ≫ fst H.X K.X ≫ j.hom.hom) *
    (y ≫ snd H.X K.X ≫ i.hom.hom) = g
  rw [← MonObj.comp_mul]
  change (g ≫ inv m.hom.hom) ≫ m.hom.hom = g
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- A normal subgroup of the first factor is normal in the whole commuting product. -/
theorem SubgroupFunctor.IsNormal.range_comp_left_of_isIso_commutingMultiplication
    [IsIso (commutingSubgroupMultiplicationHom j i hc)]
    {a : A ⟶ H} (ha : (SubgroupFunctor.range a).IsNormal) :
    (SubgroupFunctor.range (a ≫ j)).IsNormal := by
  intro T g z _ hz
  obtain ⟨h, x, rfl⟩ := exists_factor_points_of_isIso_commutingMultiplication j i hc T g
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp
    (ha T h (y ≫ a.hom.hom) (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨v, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hv, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  change ((h ≫ j.hom.hom) * ((y ≫ a.hom.hom) ≫ j.hom.hom)) *
      (h ≫ j.hom.hom)⁻¹ =
    ((h ≫ j.hom.hom) * (x ≫ i.hom.hom)) *
      ((y ≫ a.hom.hom) ≫ j.hom.hom) *
      ((h ≫ j.hom.hom) * (x ≫ i.hom.hom))⁻¹
  rw [mul_inv_rev]
  have hx := (hc T (y ≫ a.hom.hom) x).symm.mul_inv_cancel
  calc
    _ = (h ≫ j.hom.hom) *
        ((x ≫ i.hom.hom) * ((y ≫ a.hom.hom) ≫ j.hom.hom) *
          (x ≫ i.hom.hom)⁻¹) * (h ≫ j.hom.hom)⁻¹ := by rw [hx]
    _ = _ := by simp only [mul_assoc]

/-- A normal subgroup of the second factor is normal in the whole commuting product. -/
theorem SubgroupFunctor.IsNormal.range_comp_right_of_isIso_commutingMultiplication
    [IsIso (commutingSubgroupMultiplicationHom j i hc)]
    {a : A ⟶ K} (ha : (SubgroupFunctor.range a).IsNormal) :
    (SubgroupFunctor.range (a ≫ i)).IsNormal := by
  intro T g z _ hz
  obtain ⟨h, x, rfl⟩ := exists_factor_points_of_isIso_commutingMultiplication j i hc T g
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp
    (ha T x (y ≫ a.hom.hom) (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨v, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hv, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  change ((x ≫ i.hom.hom) * ((y ≫ a.hom.hom) ≫ i.hom.hom)) *
      (x ≫ i.hom.hom)⁻¹ =
    ((h ≫ j.hom.hom) * (x ≫ i.hom.hom)) *
      ((y ≫ a.hom.hom) ≫ i.hom.hom) *
      ((h ≫ j.hom.hom) * (x ≫ i.hom.hom))⁻¹
  rw [(hc T h x).eq, mul_inv_rev]
  have hh := (hc T h (y ≫ a.hom.hom)).mul_inv_cancel
  calc
    _ = (x ≫ i.hom.hom) *
        ((h ≫ j.hom.hom) * ((y ≫ a.hom.hom) ≫ i.hom.hom) *
          (h ≫ j.hom.hom)⁻¹) * (x ≫ i.hom.hom)⁻¹ := by rw [hh]
    _ = _ := by simp only [mul_assoc]

/-- If the second factor alone is already the whole product, the first range is trivial. -/
theorem range_left_eq_bot_of_isIso_right_commutingMultiplication
    [IsIso (commutingSubgroupMultiplicationHom j i hc)] [IsIso i] :
    SubgroupFunctor.range j = ⊥ := by
  let m := commutingSubgroupMultiplicationHom j i hc
  have : IsIso m.hom.hom := (Grp.forget (Over S)).map_isIso m
  have : IsIso i.hom.hom := (Grp.forget (Over S)).map_isIso i
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  let x := (h ≫ j.hom.hom) ≫ inv i.hom.hom
  have heq : lift h (1 : T ⟶ K.X) = lift (1 : T ⟶ H.X) x := by
    apply (cancel_mono m.hom.hom).mp
    change lift h 1 ≫ subgroupMultiplication j i =
      lift 1 x ≫ subgroupMultiplication j i
    rw [comp_subgroupMultiplication, comp_subgroupMultiplication,
      MonObj.one_comp, MonObj.one_comp, mul_one, one_mul]
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hh := congrArg (fun t => t ≫ fst H.X K.X) heq
  simp only [lift_fst] at hh
  rw [hh, MonObj.one_comp]

end Base

section RationalPoints

variable {k : Type u} [CommRing k]
variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- A subgroup containing both factor images of an isomorphic multiplication is full. -/
theorem rationalPoints.subgroup_eq_top_of_isIso_commutingMultiplication
    (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    [IsIso (commutingSubgroupMultiplicationHom j i hc)]
    (L : Subgroup (rationalPoints G))
    (hj : (rationalPoints.map j).range ≤ L)
    (hi : (rationalPoints.map i).range ≤ L) : L = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨h, x, rfl⟩ :=
    exists_factor_points_of_isIso_commutingMultiplication j i hc _ g
  exact L.mul_mem (hj ⟨h, rfl⟩) (hi ⟨x, rfl⟩)

end RationalPoints

end Langlands.GroupScheme
