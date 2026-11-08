import Langlands.GroupScheme.Rational.RootQuotientLieEquiv

/-! # Linearity of the Heisenberg cocycle under the point-to-Lie comparisons

Let `a` be a multipliable relative root, `V = U_a / U_{2a}`, and let `β` be the cocycle of a
Heisenberg normal form. The rational points of `V` and of `U_{2a}` are identified with the
weight spaces of `a` and of `2 • a` in the Lie algebra of `G`. Through these identifications,
`β` on rational points is `k`-linear in each argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot


variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom]
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

variable (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)

include hS ha in
omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom] in
theorem two_nsmul_ne_zero_of_isSplitTorus : 2 • a ≠ 0 :=
  hS.nsmul_ne_zero ha (by omega)

omit [IsAffineHom U.X.hom] in
/-- The rational points of a represented doubled root group as weight vectors of `2 • a`. -/
def doubleRootPointLieEquiv (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂) :
    Additive (rationalPoints U₂) ≃+ weightSpace i (2 • a) :=
  (hj₂.pointsEquiv (Over.mk (𝟙 _))).toAdditive.trans
    (representedRootPointLieEquiv hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
      (hasNoHigherRoots_two_nsmul hhigh) hj₂)

omit [IsAffineHom U.X.hom] in
/-- The doubled-root comparison is the differential of the inclusion applied to the
point-to-Lie comparison in weight vector coordinates. -/
theorem doubleRootPointLieEquiv_apply (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂)
    (w : rationalPoints U₂) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul w) : Additive (lieKernel G k)) =
      Lie.targetMapLinear j₂ k
        (vectorPointLieEquiv (weightVectorCoordinatesOfNoHigherRoots hS i
            (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
          (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
            (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property.1 (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U₂ w))) :=
  representedRootPointLieEquiv_apply hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
    (hasNoHigherRoots_two_nsmul hhigh) hj₂ w

namespace DoubleRootCommutatorPairing

variable (C : DoubleRootCommutatorPairing i a hj hj₂) [IsAffineHom C.V.X.hom]

omit [IsAffineHom U₂.X.hom] in
/-- If two rational points of the quotient have proportional images in the weight space of `a`,
their images under the point-to-Lie comparison of the chosen weight coordinates are
proportional. -/
theorem vectorPointLieEquiv_smul_of_rootQuotientPointLieEquiv (c : k) (v v' : rationalPoints C.V)
    (h : (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul v') :
        Additive (lieKernel G k)) =
      c • (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul v) :
        Additive (lieKernel G k))) :
    vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k C.V v')) =
      c • vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k C.V v)) := by
  let f : Additive (lieKernel C.V k) →ₗ[k] Additive (lieKernel G k) :=
    (weightSpace i a).subtype ∘ₗ (C.rootQuotientLieEquiv hS ha hhigh).symm.toLinearMap
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (C.rootQuotientLieEquiv hS ha hhigh).symm.injective
  apply hf
  rw [map_smul]
  exact h

variable {C} in
omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom]
  [IsAffineHom C.V.X.hom] in
/-- The rational coefficient comparison commutes with evaluating the cocycle. -/
theorem rationalCoeffEquiv_lift_comp (M : HeisenbergNormalForm C) (x y : rationalPoints C.V) :
    GaloisPointComparison.rationalCoeffEquiv k U₂ (lift x y ≫ M.cocycle) =
      lift (GaloisPointComparison.rationalCoeffEquiv k C.V x)
        (GaloisPointComparison.rationalCoeffEquiv k C.V y) ≫ M.cocycle := by
  change (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ (lift x y ≫ M.cocycle) =
    lift ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ x)
      ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ y) ≫ M.cocycle
  rw [← Category.assoc, comp_lift]

variable {C} in
omit [IsAffineHom U.X.hom] in
/-- In the point-to-Lie comparisons of weight vector coordinates, scaling the first argument of
the cocycle by a scalar scales its value, for points with coefficients in `k`. -/
theorem vectorPointLieEquiv_cocycle_smul_left (M : HeisenbergNormalForm C)
    (r : CommAlgCat.of k k) (x x' y : Lie.AffinePoints C.V (CommAlgCat.of k k))
    (h : vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul x') =
      r • vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul x)) :
    vectorPointLieEquiv (weightVectorCoordinatesOfNoHigherRoots hS i
        (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
      (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
        (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property.1 (CommAlgCat.of k k)
      (Additive.ofMul (lift x' y ≫ M.cocycle)) =
    r • vectorPointLieEquiv (weightVectorCoordinatesOfNoHigherRoots hS i
        (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
      (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
        (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property.1 (CommAlgCat.of k k)
      (Additive.ofMul (lift x y ≫ M.cocycle)) := by
  have hw := C.weightVectorStructure.1.choose_spec.choose_spec
  have hw₂ := (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
    (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property
  have hcp : ∀ x y : Lie.AffinePoints C.V (CommAlgCat.of k k),
      (vectorAffineCoordinates (weightVectorCoordinatesOfNoHigherRoots hS i
          (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
        (CommAlgCat.of k k) (lift x y ≫ M.cocycle)).toAdd =
      coordinatePairing C.weightVectorStructure.1.choose_spec.choose
        (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
          (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val M.cocycle (A := CommAlgCat.of k k)
        (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose (CommAlgCat.of k k)
          x).toAdd
        (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose (CommAlgCat.of k k)
          y).toAdd := by
    intro x y
    simp only [coordinatePairing, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hx : (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose
      (CommAlgCat.of k k) x').toAdd =
      r • (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose
        (CommAlgCat.of k k) x).toAdd := by
    change (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm _ =
      r • (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm _ at h
    rw [← map_smul] at h
    exact (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm.injective h
  change (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm _ =
    r • (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm _
  rw [← map_smul]
  refine congrArg (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm ?_
  refine (hcp x' y).trans ?_
  rw [hx, (coordinatePairing_smul hS ha hw hw₂ (fun _ s x y => M.cocycle_act s x y)
    (fun _ y => M.cocycle_one_left y) (fun _ x => M.cocycle_one_right x) r _ _).1]
  exact congrArg (r • ·) (hcp x y).symm

variable {C} in
omit [IsAffineHom U.X.hom] in
/-- In the point-to-Lie comparisons of weight vector coordinates, scaling the second argument of
the cocycle by a scalar scales its value, for points with coefficients in `k`. -/
theorem vectorPointLieEquiv_cocycle_smul_right (M : HeisenbergNormalForm C)
    (r : CommAlgCat.of k k) (x y y' : Lie.AffinePoints C.V (CommAlgCat.of k k))
    (h : vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul y') =
      r • vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
        C.weightVectorStructure.1.choose_spec.choose_spec.1
        (CommAlgCat.of k k) (Additive.ofMul y)) :
    vectorPointLieEquiv (weightVectorCoordinatesOfNoHigherRoots hS i
        (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
      (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
        (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property.1 (CommAlgCat.of k k)
      (Additive.ofMul (lift x y' ≫ M.cocycle)) =
    r • vectorPointLieEquiv (weightVectorCoordinatesOfNoHigherRoots hS i
        (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
      (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
        (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property.1 (CommAlgCat.of k k)
      (Additive.ofMul (lift x y ≫ M.cocycle)) := by
  have hw := C.weightVectorStructure.1.choose_spec.choose_spec
  have hw₂ := (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
    (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.property
  have hcp : ∀ x y : Lie.AffinePoints C.V (CommAlgCat.of k k),
      (vectorAffineCoordinates (weightVectorCoordinatesOfNoHigherRoots hS i
          (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val
        (CommAlgCat.of k k) (lift x y ≫ M.cocycle)).toAdd =
      coordinatePairing C.weightVectorStructure.1.choose_spec.choose
        (weightVectorCoordinatesOfNoHigherRoots hS i (two_nsmul_ne_zero_of_isSplitTorus hS ha)
          (hasNoHigherRoots_two_nsmul hhigh) hj₂).2.val M.cocycle (A := CommAlgCat.of k k)
        (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose (CommAlgCat.of k k)
          x).toAdd
        (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose (CommAlgCat.of k k)
          y).toAdd := by
    intro x y
    simp only [coordinatePairing, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hy : (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose
      (CommAlgCat.of k k) y').toAdd =
      r • (vectorAffineCoordinates C.weightVectorStructure.1.choose_spec.choose
        (CommAlgCat.of k k) y).toAdd := by
    change (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm _ =
      r • (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm _ at h
    rw [← map_smul] at h
    exact (vectorLieCoordinates _ hw.1 (CommAlgCat.of k k)).symm.injective h
  change (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm _ =
    r • (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm _
  rw [← map_smul]
  refine congrArg (vectorLieCoordinates _ hw₂.1 (CommAlgCat.of k k)).symm ?_
  refine (hcp x y').trans ?_
  rw [hy, (coordinatePairing_smul hS ha hw hw₂ (fun _ s x y => M.cocycle_act s x y)
    (fun _ y => M.cocycle_one_left y) (fun _ x => M.cocycle_one_right x) r _ _).2]
  exact congrArg (r • ·) (hcp x y).symm

variable {C} in
include hS ha hhigh in
/-- **Linearity in the first argument.** If the image of `v'` in the weight space of `a` is `c`
times that of `v`, then the image of the cocycle at `(v', w)` in the weight space of `2 • a` is
`c` times that at `(v, w)`. -/
theorem doubleRootPointLieEquiv_cocycle_smul_left (M : HeisenbergNormalForm C) (c : k)
    (v v' w : rationalPoints C.V)
    (h : (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul v') :
        Additive (lieKernel G k)) =
      c • (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul v) :
        Additive (lieKernel G k))) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (lift v' w ≫ M.cocycle)) :
        Additive (lieKernel G k)) =
      c • (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (lift v w ≫ M.cocycle)) :
        Additive (lieKernel G k)) := by
  have h' := C.vectorPointLieEquiv_smul_of_rootQuotientPointLieEquiv hS ha hhigh c v v' h
  have key := vectorPointLieEquiv_cocycle_smul_left hS ha hhigh M (c : CommAlgCat.of k k)
    (GaloisPointComparison.rationalCoeffEquiv k C.V v)
    (GaloisPointComparison.rationalCoeffEquiv k C.V v')
    (GaloisPointComparison.rationalCoeffEquiv k C.V w) h'
  rw [doubleRootPointLieEquiv_apply, doubleRootPointLieEquiv_apply,
    rationalCoeffEquiv_lift_comp M v' w, rationalCoeffEquiv_lift_comp M v w, key]
  exact map_smul (Lie.targetMapLinear j₂ k) c _

variable {C} in
include hS ha hhigh in
/-- **Linearity in the second argument.** If the image of `w'` in the weight space of `a` is `c`
times that of `w`, then the image of the cocycle at `(v, w')` in the weight space of `2 • a` is
`c` times that at `(v, w)`. -/
theorem doubleRootPointLieEquiv_cocycle_smul_right (M : HeisenbergNormalForm C) (c : k)
    (v w w' : rationalPoints C.V)
    (h : (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul w') :
        Additive (lieKernel G k)) =
      c • (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul w) :
        Additive (lieKernel G k))) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (lift v w' ≫ M.cocycle)) :
        Additive (lieKernel G k)) =
      c • (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (lift v w ≫ M.cocycle)) :
        Additive (lieKernel G k)) := by
  have h' := C.vectorPointLieEquiv_smul_of_rootQuotientPointLieEquiv hS ha hhigh c w w' h
  have key := vectorPointLieEquiv_cocycle_smul_right hS ha hhigh M (c : CommAlgCat.of k k)
    (GaloisPointComparison.rationalCoeffEquiv k C.V v)
    (GaloisPointComparison.rationalCoeffEquiv k C.V w)
    (GaloisPointComparison.rationalCoeffEquiv k C.V w') h'
  rw [doubleRootPointLieEquiv_apply, doubleRootPointLieEquiv_apply,
    rationalCoeffEquiv_lift_comp M v w', rationalCoeffEquiv_lift_comp M v w, key]
  exact map_smul (Lie.targetMapLinear j₂ k) c _

end DoubleRootCommutatorPairing

end Langlands.GroupScheme.RelativeRoot
