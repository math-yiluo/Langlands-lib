import Langlands.GroupScheme.Absolute.RationalPointClosureStatement
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Absolute.Borel
import Langlands.AbelianScheme.KernelBaseChange

/-! # Solvability of the closure of a group of rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

section Closure

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The rational points of `H` located in the closure of the locations of the points in `S`. -/
def rationalPointClosure (S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :
    Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
  {x | x.left (IsLocalRing.closedPoint k) ∈ closure (rationalPointImage H S)}

variable {H}

theorem subset_rationalPointClosure (S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :
    S ⊆ rationalPointClosure H S :=
  fun x hx => subset_closure ⟨x, hx, rfl⟩

theorem rationalPointClosure_mono {S S' : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    (h : S ⊆ S') : rationalPointClosure H S ⊆ rationalPointClosure H S' :=
  fun _ hx => closure_mono (Set.image_mono h) hx

/-- A morphism `φ` sending the points of `S` into the closure of `S'` sends the points in the
closure of `S` into the closure of `S'`, by continuity. -/
theorem comp_mem_rationalPointClosure
    {S S' : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)} (φ : H.X ⟶ H.X)
    (hφ : ∀ s ∈ S, s ≫ φ ∈ rationalPointClosure H S')
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X} (hx : x ∈ rationalPointClosure H S) :
    x ≫ φ ∈ rationalPointClosure H S' := by
  have himage : φ.left '' rationalPointImage H S ⊆ closure (rationalPointImage H S') := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact hφ s hs
  have h := image_closure_subset_closure_image φ.left.continuous ⟨_, hx, rfl⟩
  change φ.left (x.left (IsLocalRing.closedPoint k)) ∈ closure (rationalPointImage H S')
  exact closure_minimal himage isClosed_closure h

/-- A binary operation on points that is given by morphisms in each variable separately sends
the closures of `A` and `B` into the closure of `C` once it sends `A` and `B` there. -/
theorem mem_rationalPointClosure_of_binary
    {A B C : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    (w : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) →
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) →
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X))
    (hl : ∀ a, ∃ φ : H.X ⟶ H.X, ∀ y, y ≫ φ = w a y)
    (hr : ∀ b, ∃ ψ : H.X ⟶ H.X, ∀ x, x ≫ ψ = w x b)
    (h : ∀ a ∈ A, ∀ b ∈ B, w a b ∈ rationalPointClosure H C)
    {x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X}
    (hx : x ∈ rationalPointClosure H A) (hy : y ∈ rationalPointClosure H B) :
    w x y ∈ rationalPointClosure H C := by
  have step : ∀ a ∈ A, w a y ∈ rationalPointClosure H C := by
    intro a ha
    obtain ⟨φ, hφ⟩ := hl a
    rw [← hφ]
    exact comp_mem_rationalPointClosure φ (fun b hb => (hφ b).symm ▸ h a ha b hb) hy
  obtain ⟨ψ, hψ⟩ := hr y
  rw [← hψ]
  exact comp_mem_rationalPointClosure ψ (fun a ha => (hψ a).symm ▸ step a ha) hx

theorem comp_constantPoint (a y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    y ≫ H.constantPoint a H.X = a := by
  rw [H.constantPoint_naturality, constantPoint_self]

theorem exists_comp_eq_mul_left (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    ∃ φ : H.X ⟶ H.X, ∀ y, y ≫ φ = a * y :=
  ⟨H.constantPoint a H.X * 𝟙 H.X, fun y => by
    rw [MonObj.comp_mul, comp_constantPoint, Category.comp_id]⟩

theorem exists_comp_eq_mul_right (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    ∃ ψ : H.X ⟶ H.X, ∀ x, x ≫ ψ = x * b :=
  ⟨𝟙 H.X * H.constantPoint b H.X, fun x => by
    rw [MonObj.comp_mul, comp_constantPoint, Category.comp_id]⟩

theorem comp_commutatorElement {T : Over (Spec (CommRingCat.of k))} (y : T ⟶ H.X)
    (f g : H.X ⟶ H.X) : y ≫ ⁅f, g⁆ = ⁅y ≫ f, y ≫ g⁆ := by
  simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv]

theorem exists_comp_eq_commutator_left (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    ∃ φ : H.X ⟶ H.X, ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, y ≫ φ = ⁅a, y⁆ :=
  ⟨⁅H.constantPoint a H.X, 𝟙 H.X⁆, fun y => by
    rw [comp_commutatorElement, comp_constantPoint, Category.comp_id]⟩

theorem exists_comp_eq_commutator_right (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    ∃ ψ : H.X ⟶ H.X, ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, x ≫ ψ = ⁅x, b⁆ :=
  ⟨⁅𝟙 H.X, H.constantPoint b H.X⁆, fun x => by
    rw [comp_commutatorElement, comp_constantPoint, Category.comp_id]⟩

variable (H) in
/-- The rational points in the closure of the locations of a group of rational points form a
group. -/
def pointClosureSubgroup (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) where
  carrier := rationalPointClosure H Γ
  mul_mem' hx hy := mem_rationalPointClosure_of_binary (· * ·) exists_comp_eq_mul_left
    exists_comp_eq_mul_right
    (fun _ ha _ hb => subset_rationalPointClosure _ (Γ.mul_mem ha hb)) hx hy
  one_mem' := subset_rationalPointClosure _ Γ.one_mem
  inv_mem' {x} hx := by
    have h := comp_mem_rationalPointClosure (S' := Γ) (𝟙 H.X)⁻¹ (fun s hs => by
      rw [GrpObj.comp_inv, Category.comp_id]
      exact subset_rationalPointClosure _ (Γ.inv_mem hs)) hx
    rwa [GrpObj.comp_inv, Category.comp_id] at h

theorem mem_pointClosureSubgroup {Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X} :
    x ∈ pointClosureSubgroup H Γ ↔ x.left (IsLocalRing.closedPoint k) ∈
      closure (rationalPointImage H (Γ : Set _)) :=
  Iff.rfl

theorem le_pointClosureSubgroup (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :
    Γ ≤ pointClosureSubgroup H Γ :=
  subset_rationalPointClosure _

theorem pointClosureSubgroup_mono {Γ Γ' : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    (h : Γ ≤ Γ') : pointClosureSubgroup H Γ ≤ pointClosureSubgroup H Γ' :=
  rationalPointClosure_mono h

/-- The commutator of the closures lies in the closure of the commutator. -/
theorem commutator_pointClosureSubgroup_le
    (A B : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :
    ⁅pointClosureSubgroup H A, pointClosureSubgroup H B⁆ ≤ pointClosureSubgroup H ⁅A, B⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact mem_rationalPointClosure_of_binary (fun a b => ⁅a, b⁆) exists_comp_eq_commutator_left
    exists_comp_eq_commutator_right
    (fun _ ha _ hb => subset_rationalPointClosure _ (Subgroup.commutator_mem_commutator ha hb))
    hx hy

/-- Over an algebraically closed field, the location of a rational point is a closed point. -/
theorem isClosed_singleton_rationalPoint [IsAlgClosed k] [LocallyOfFiniteType H.X.hom]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    IsClosed {x.left (IsLocalRing.closedPoint k)} :=
  ((pointEquivClosedPoint H.X.hom) ⟨x.left, Over.w x⟩).2

/-- Over an algebraically closed field, rational points are determined by their locations. -/
theorem rationalPoint_ext [IsAlgClosed k] [LocallyOfFiniteType H.X.hom]
    {x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X}
    (h : x.left (IsLocalRing.closedPoint k) = y.left (IsLocalRing.closedPoint k)) : x = y :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.X.hom (Over.w x) (Over.w y) h)

theorem pointClosureSubgroup_bot [IsAlgClosed k] [LocallyOfFiniteType H.X.hom] :
    pointClosureSubgroup H ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_pointClosureSubgroup, rationalPointImage, Subgroup.coe_bot, Set.image_singleton,
    (isClosed_singleton_rationalPoint _).closure_eq] at hx
  exact Subgroup.mem_bot.2 (rationalPoint_ext hx)

/-- The derived series of the closure lies in the closure of the derived series. -/
theorem map_derivedSeries_pointClosureSubgroup_le
    (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) (n : ℕ) :
    (derivedSeries (pointClosureSubgroup H Γ) n).map (pointClosureSubgroup H Γ).subtype ≤
      pointClosureSubgroup H ((derivedSeries Γ n).map Γ.subtype) := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, derivedSeries_zero, ← MonoidHom.range_eq_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.range_subtype]
  | succ n ih =>
    rw [derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator,
      Subgroup.map_commutator]
    exact (Subgroup.commutator_mono ih ih).trans (commutator_pointClosureSubgroup_le _ _)

/-- Over an algebraically closed field, the closure of a solvable group of rational points is
solvable. -/
theorem isSolvable_pointClosureSubgroup [IsAlgClosed k] [LocallyOfFiniteType H.X.hom]
    (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) [hΓ : Group.IsSolvable Γ] :
    Group.IsSolvable (pointClosureSubgroup H Γ) := by
  obtain ⟨n, hn⟩ := hΓ.solvable
  refine ⟨⟨n, ?_⟩⟩
  rw [← Subgroup.map_eq_bot_iff_of_injective _ (pointClosureSubgroup H Γ).subtype_injective,
    eq_bot_iff]
  refine (map_derivedSeries_pointClosureSubgroup_le Γ n).trans ?_
  rw [hn, Subgroup.map_bot, pointClosureSubgroup_bot]

end Closure

section AlgClosed

variable (k : Type u) [Field k] [IsAlgClosed k]

instance isIso_toAlgebraicClosure : IsIso (toAlgebraicClosure k) := by
  have : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := AlgebraicClosure k))
  dsimp only [toAlgebraicClosure]
  infer_instance

/-- Over an algebraically closed field `k`, the test scheme `Spec k̄ ⟶ Spec k` is isomorphic to
the identity test scheme. -/
def algebraicClosurePointIso :
    (Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ≅
      Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.isoMk (asIso (toAlgebraicClosure k)) (by simp)

variable {k}

/-- Points of a group object on isomorphic test objects form isomorphic groups. -/
def pointsMulEquivOfIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {T T' : C}
    (e : T ≅ T') (G : C) [GrpObj G] : (T' ⟶ G) ≃* (T ⟶ G) where
  toFun x := e.hom ≫ x
  invFun y := e.inv ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

/-- Over an algebraically closed field `k`, a group scheme is solvable exactly when its group of
`k`-points is solvable. -/
theorem isSolvableGroupScheme_iff_isSolvable_points (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSolvableGroupScheme G ↔
      Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) := by
  let e := (baseChangePointsEquiv (toAlgebraicClosure k) G
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).trans
      (pointsMulEquivOfIso (algebraicClosurePointIso k) G.X).symm
  constructor
  · intro h
    have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) := h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro h
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

end AlgClosed

end Langlands.GroupScheme
