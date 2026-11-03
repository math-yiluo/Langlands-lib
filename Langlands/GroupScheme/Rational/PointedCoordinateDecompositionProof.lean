import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionStatement
import Langlands.GroupScheme.Rational.PointedCoordinateCoaction
import Langlands.GroupScheme.Torus.CharacterActionGrading
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.LinearAlgebra.FinsuppDecomposition

/-! # Split-torus decomposition of actual pointed affine coordinates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PointedCoordinateWeights

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {I : Type u} [Fintype I] [DecidableEq I]
  (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

section TorusPoints

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The actual point of `S` whose coordinates under `e` are the values of `t` at the
standard basis vectors of `ℤ^I`. -/
def torusPoint (t : Multiplicative (I → ℤ) →* Aˣ) : Lie.AffinePoints S.toGrp A :=
  (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
      (fun i => t (Multiplicative.ofAdd (Pi.single i 1))) ≫ e.inv.hom.hom

theorem torusPoint_one : torusPoint e (1 : Multiplicative (I → ℤ) →* Aˣ) = 1 := by
  have h : (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
      (fun i => (1 : Multiplicative (I → ℤ) →* Aˣ) (Multiplicative.ofAdd (Pi.single i 1))) =
        1 :=
    map_one (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
  rw [torusPoint, h]
  have h1 := map_one (isoPointsEquiv e.symm
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))))
  rw [isoPointsEquiv_apply] at h1
  exact h1

theorem torusPoint_mul (t s : Multiplicative (I → ℤ) →* Aˣ) :
    torusPoint e (t * s) = torusPoint e t * torusPoint e s := by
  have h : (fun i => (t * s) (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))) =
      (fun i => t (Multiplicative.ofAdd (Pi.single i 1))) *
        (fun i => s (Multiplicative.ofAdd (Pi.single i 1))) := rfl
  rw [torusPoint, torusPoint, torusPoint, h, map_mul]
  have h1 := map_mul (isoPointsEquiv e.symm
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))))
    ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
      (fun i => t (Multiplicative.ofAdd (Pi.single i 1))))
    ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
      (fun i => s (Multiplicative.ofAdd (Pi.single i 1))))
  rw [isoPointsEquiv_apply, isoPointsEquiv_apply, isoPointsEquiv_apply] at h1
  exact h1

theorem torusPoint_map (f : A →ₐ[k] B) (t : Multiplicative (I → ℤ) →* Aˣ) :
    torusPoint e ((Units.map f.toRingHom.toMonoidHom).comp t) =
      Lie.affineMap S.toGrp f (torusPoint e t) := by
  have h : (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I B).symm
      (fun i => ((Units.map f.toRingHom.toMonoidHom).comp t)
        (Multiplicative.ofAdd (Pi.single i 1))) =
      Lie.affineMap _ f ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
        (fun i => t (Multiplicative.ofAdd (Pi.single i 1)))) := by
    apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I B).injective
    rw [splitTorus.algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    rfl
  rw [torusPoint, torusPoint, h, Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]

/-- A homomorphism on `Multiplicative ℤ^I` is the exponent evaluation at its values on the
standard basis vectors. -/
theorem exponentValue_hom (t : Multiplicative (I → ℤ) →* Aˣ) (m : I → ℤ) :
    splitTorus.exponentValue I (fun i => t (Multiplicative.ofAdd (Pi.single i 1)))
      (Multiplicative.ofAdd m) = t (Multiplicative.ofAdd m) := by
  have hm : (∑ i, m i • Pi.single i (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  calc splitTorus.exponentValue I (fun i => t (Multiplicative.ofAdd (Pi.single i 1)))
        (Multiplicative.ofAdd m) = ∏ i, t (Multiplicative.ofAdd (Pi.single i 1)) ^ m i := rfl
    _ = ∏ i, t (Multiplicative.ofAdd (m i • Pi.single i (1 : ℤ))) := by
        simp only [ofAdd_zsmul, map_zpow]
    _ = t (Multiplicative.ofAdd (∑ i, m i • Pi.single i (1 : ℤ))) := by
        rw [ofAdd_sum, map_prod]
    _ = t (Multiplicative.ofAdd m) := by rw [hm]

/-- Exponent vectors as actual characters of `S`, transported along `e`. -/
def characterEquiv : (I → ℤ) ≃+ characterLattice S :=
  (splitTorus.characterLatticeEquiv k I).symm.trans
    (characterLattice.comapIso (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e)

theorem characterValue_torusPoint (t : Multiplicative (I → ℤ) →* Aˣ) (m : I → ℤ) :
    Lie.characterValue (characterEquiv e m) (torusPoint e t) = t (Multiplicative.ofAdd m) := by
  change Lie.characterValue ((Additive.ofMul e.hom :
      S ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) ≫
    (splitTorus.characterLatticeEquiv k I).symm m) (torusPoint e t) = _
  rw [Lie.characterValue_comp]
  change Lie.characterValue ((splitTorus.characterLatticeEquiv k I).symm m)
    (torusPoint e t ≫ e.hom.hom.hom) = _
  have ht : torusPoint e t ≫ e.hom.hom.hom =
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm
        (fun i => t (Multiplicative.ofAdd (Pi.single i 1))) := by
    rw [torusPoint, Category.assoc]
    change _ ≫ (e.inv ≫ e.hom).hom.hom = _
    rw [e.inv_hom_id]
    exact Category.comp_id _
  rw [ht, splitTorus.characterValue_characterLatticeEquiv_symm, MulEquiv.apply_symm_apply,
    exponentValue_hom]

/-- The exponent character of an actual point of `S`. -/
def pointCharacter (s : Lie.AffinePoints S.toGrp A) : Multiplicative (I → ℤ) →* Aˣ :=
  splitTorus.exponentValue I
    (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A (s ≫ e.hom.hom.hom))

theorem torusPoint_pointCharacter (s : Lie.AffinePoints S.toGrp A) :
    torusPoint e (pointCharacter e s) = s := by
  have h : (fun i => pointCharacter e s (Multiplicative.ofAdd (Pi.single i 1))) =
      splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A (s ≫ e.hom.hom.hom) := by
    funext i
    exact splitTorus.exponentValue_single I _ i
  rw [torusPoint, h, MulEquiv.symm_apply_apply, Category.assoc]
  change s ≫ (e.hom ≫ e.inv).hom.hom = s
  rw [e.hom_inv_id]
  exact Category.comp_id s

theorem characterValue_eq_pointCharacter (s : Lie.AffinePoints S.toGrp A) (m : I → ℤ) :
    Lie.characterValue (characterEquiv e m) s = pointCharacter e s (Multiplicative.ofAdd m) := by
  conv_lhs => rw [← torusPoint_pointCharacter e s]
  exact characterValue_torusPoint e _ m

end TorusPoints

variable {V : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom] (a : PointedAction S V)

/-- The actual pointed action, read as a natural action of the exponent character functor
on the algebra-valued points of the actual coordinate algebra. -/
def characterAction :
    CharacterAction.Action (R := CommRingCat.of k) (M := I → ℤ) (Coord V) where
  act {C} t x := CommAlgCat.ofHom
    (pointCoordinates (a.act (torusPoint e t) (pointCoordinates.symm x.hom)))
  one {C} x := by
    rw [torusPoint_one, PointedAction.act_one_left, Equiv.apply_symm_apply]
    rfl
  mul {C} t s x := by
    rw [torusPoint_mul, PointedAction.act_mul_left]
    simp only [CommAlgCat.hom_ofHom, Equiv.symm_apply_apply]
  naturality {C D} f t x := by
    apply CommAlgCat.hom_ext
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp]
    have hx : (pointCoordinates.symm (f.hom.comp x.hom) : Points V D) =
        pointsMap f.hom (pointCoordinates.symm x.hom) := by
      apply pointCoordinates.injective
      rw [Equiv.apply_symm_apply, pointCoordinates_naturality, Equiv.apply_symm_apply]
    rw [torusPoint_map e f.hom t, hx, ← pointCoordinates_naturality]
    congr 1
    rw [Lie.affineMap_apply, pointsMap, pointsMap, ← a.naturality]

/-- The coaction of the actual pointed action: its value at the universal exponent
character and the universal point. -/
abbrev coaction : Coord V ⟶ CharacterAction.algebra (M := I → ℤ) (Coord V) :=
  CharacterAction.coaction (characterAction e a)

theorem pointCoordinates_act_eq {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) (v : Points V A) :
    pointCoordinates (a.act s v) =
      (coaction e a ≫ CharacterAction.evaluate (C := CommAlgCat.of (CommRingCat.of k) A)
        (CommAlgCat.ofHom (pointCoordinates v)) (pointCharacter e s)).hom := by
  rw [← CharacterAction.act_eq_coaction_evaluate]
  change pointCoordinates (a.act s v) = pointCoordinates
    (a.act (torusPoint e (pointCharacter e s)) (pointCoordinates.symm (pointCoordinates v)))
  rw [torusPoint_pointCharacter, Equiv.symm_apply_apply]

/-- Every coaction coefficient satisfies the all-algebra eigencondition for its character. -/
theorem coaction_coeff_mem (z : Coord V) (m : I → ℤ) :
    ((coaction e a).hom z).coeff m ∈ weightSpace a (characterEquiv e m) := by
  intro A _ _ s v
  rw [pointCoordinates_act_eq e a s v, CommAlgCat.hom_comp, AlgHom.comp_apply,
    CharacterAction.coaction_coefficient_homogeneous, CharacterAction.evaluate_single,
    characterValue_eq_pointCharacter, mul_comm]
  rfl

/-- On an eigenspace, the coaction is the corresponding monomial. -/
theorem coaction_of_mem (m : I → ℤ) (z : Coord V)
    (hz : z ∈ weightSpace a (characterEquiv e m)) :
    (coaction e a).hom z = AddMonoidAlgebra.single m z := by
  have h := hz (AddMonoidAlgebra (Coord V) (I → ℤ))
    (torusPoint e (CharacterAction.universal (Coord V)))
    (pointCoordinates.symm (CharacterAction.constant (M := I → ℤ) (Coord V)).hom)
  rw [characterValue_torusPoint, Equiv.apply_symm_apply] at h
  refine h.trans ?_
  change AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single 0 z = _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

omit [Fintype I] [DecidableEq I] in
theorem evaluate_one_apply (q : AddMonoidAlgebra (Coord V) (I → ℤ)) :
    (CharacterAction.evaluate (𝟙 (Coord V))
      (1 : Multiplicative (I → ℤ) →* (Coord V)ˣ)).hom q = q.coeff.sum (fun _ y => y) := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | single m b =>
    rw [CharacterAction.evaluate_single, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index] <;> simp

/-- The coaction coefficients sum to the original coordinate function. -/
theorem coaction_sum (z : Coord V) :
    ((coaction e a).hom z).coeff.sum (fun _ y => y) = z := by
  have h := congrArg (fun f : Coord V ⟶ Coord V => f.hom z)
    (CharacterAction.coaction_counit (characterAction e a))
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_id, AlgHom.id_apply] at h
  rw [evaluate_one_apply] at h
  exact h

/-- The character-indexed coaction coefficients. -/
def coefficients : Coord V →ₗ[k] (characterLattice S →₀ Coord V) :=
  (Finsupp.lmapDomain (Coord V) k (characterEquiv e)).comp
    ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (coaction e a).hom.toLinearMap)

theorem coefficients_apply (z : Coord V) (m : I → ℤ) :
    coefficients e a z (characterEquiv e m) = ((coaction e a).hom z).coeff m :=
  Finsupp.mapDomain_apply_of_injective (characterEquiv e).injective _ m

theorem coefficients_mem (z : Coord V) (χ : characterLattice S) :
    coefficients e a z χ ∈ weightSpace a χ := by
  obtain ⟨m, rfl⟩ := (characterEquiv e).surjective χ
  rw [coefficients_apply]
  exact coaction_coeff_mem e a z m

theorem coefficients_of_mem (χ : characterLattice S) (z : Coord V) (hz : z ∈ weightSpace a χ) :
    coefficients e a z = Finsupp.single χ z := by
  obtain ⟨m, rfl⟩ := (characterEquiv e).surjective χ
  change Finsupp.mapDomain (characterEquiv e) ((coaction e a).hom z).coeff = _
  rw [coaction_of_mem e a m z hz, AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single]

theorem coefficients_sum (z : Coord V) : (coefficients e a z).sum (fun _ y => y) = z := by
  change (Finsupp.mapDomain (characterEquiv e) ((coaction e a).hom z).coeff).sum
    (fun _ y => y) = z
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact coaction_sum e a z

include e in
theorem isInternal_weightSpace [DecidableEq (characterLattice S)] :
    DirectSum.IsInternal (weightSpace a) :=
  Langlands.LinearAlgebra.isInternal_of_finsupp _ (coefficients e a) (coefficients_mem e a)
    (fun χ z => coefficients_of_mem e a χ z z.property) (coefficients_sum e a)

/-- Evaluation at the fixed point of each coaction coefficient. -/
theorem coordinateOrigin_coaction_coeff (z : Coord V) (m : I → ℤ) :
    coordinateOrigin a (((coaction e a).hom z).coeff m) =
      (AddMonoidAlgebra.single (0 : I → ℤ) (coordinateOrigin a z)).coeff m := by
  let K : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) k
  let x : Coord V ⟶ K := CommAlgCat.ofHom (coordinateOrigin a)
  have hc : (x ≫ CharacterAction.constant (M := I → ℤ) K).hom =
      (Algebra.ofId k (AddMonoidAlgebra k (I → ℤ))).comp (coordinateOrigin a) := by
    ext y
    rfl
  have hx : (pointCoordinates.symm (x ≫ CharacterAction.constant (M := I → ℤ) K).hom :
      Points V (AddMonoidAlgebra k (I → ℤ))) = toUnit _ ≫ a.origin := by
    apply pointCoordinates.injective
    rw [Equiv.apply_symm_apply, pointCoordinates_origin, hc]
  have h2 : (characterAction e a).act (CharacterAction.universal K)
      (x ≫ CharacterAction.constant K) = x ≫ CharacterAction.constant K := by
    apply CommAlgCat.hom_ext
    change pointCoordinates (a.act _
      (pointCoordinates.symm (x ≫ CharacterAction.constant (M := I → ℤ) K).hom)) = _
    rw [hx, PointedAction.act_origin, pointCoordinates_origin, hc]
  have h3 := congrArg (fun f : Coord V ⟶ CharacterAction.algebra (M := I → ℤ) K =>
    (f.hom z).coeff m) ((CharacterAction.act_universal (characterAction e a) x).symm.trans h2)
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h3
  rw [CharacterAction.coefficientMap_coeff] at h3
  exact h3

theorem coefficients_mem_augmentation (z : Coord V) (hz : z ∈ augmentation a)
    (χ : characterLattice S) : coefficients e a z χ ∈ augmentation a := by
  obtain ⟨m, rfl⟩ := (characterEquiv e).surjective χ
  rw [coefficients_apply, mem_augmentation, coordinateOrigin_coaction_coeff,
    (mem_augmentation a).1 hz]
  simp

/-- The coefficient map restricted to the augmentation ideal. -/
def augmentationCoefficients :
    augmentation a →ₗ[k] (characterLattice S →₀ augmentation a) where
  toFun z := Finsupp.onFinset (coefficients e a z).support
    (fun χ => ⟨coefficients e a z χ, coefficients_mem_augmentation e a z z.property χ⟩)
    (by
      intro χ hχ
      rw [Finsupp.mem_support_iff]
      intro h
      exact hχ (Subtype.ext h))
  map_add' z w := by
    ext χ
    simp [Finsupp.onFinset_apply]
  map_smul' c z := by
    ext χ
    simp [Finsupp.onFinset_apply]

theorem coe_augmentationCoefficients_apply (z : augmentation a) (χ : characterLattice S) :
    (augmentationCoefficients e a z χ : Coord V) = coefficients e a z χ := rfl

theorem support_augmentationCoefficients_subset (z : augmentation a) :
    (augmentationCoefficients e a z).support ⊆ (coefficients e a z).support := by
  intro χ hχ
  rw [Finsupp.mem_support_iff] at hχ ⊢
  intro h
  apply hχ
  apply Subtype.ext
  rw [coe_augmentationCoefficients_apply, h]
  rfl

include e in
theorem isInternal_augmentationWeightSpace [DecidableEq (characterLattice S)] :
    DirectSum.IsInternal (augmentationWeightSpace a) := by
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ (augmentationCoefficients e a)
  · intro z χ
    exact coefficients_mem e a z χ
  · intro χ z
    have hz : coefficients e a ((z : augmentation a) : Coord V) =
        Finsupp.single χ ((z : augmentation a) : Coord V) :=
      coefficients_of_mem e a χ _ z.property
    ext χ'
    rw [coe_augmentationCoefficients_apply, hz, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> rfl
  · intro z
    apply Subtype.ext
    rw [Finsupp.sum_of_support_subset _ (support_augmentationCoefficients_subset e a z) _
      (fun _ _ => rfl), Submodule.coe_sum]
    exact coefficients_sum e a z

open Classical in
/-- The actual coordinate algebra and its fixed-point augmentation ideal are internal
direct sums of their character eigenspaces for every split-torus action on a pointed
affine scheme. -/
theorem pointedCoordinateDecomposition : PointedCoordinateDecompositionStatement.{u} := by
  intro k _ S hS V _ a
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let _ : Fintype I := Fintype.ofFinite I
  exact ⟨isInternal_weightSpace e a, isInternal_augmentationWeightSpace e a⟩

end Langlands.GroupScheme.PointedCoordinateWeights
