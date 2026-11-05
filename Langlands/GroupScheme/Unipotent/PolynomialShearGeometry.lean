import Langlands.GroupScheme.Unipotent.AdditiveKernelGeometry

/-! # Actual triangular additive polynomial coordinate changes -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {I : Type v} [DecidableEq I]

/-- Evaluate a triangular polynomial coordinate change along a coefficient
homomorphism on an arbitrary commutative algebra of values. -/
def polynomialShearValues {R : Type w} [CommRing R] (ρ : k →+* R)
    (j : I) (q : I → k[X]) (x : I → R) : I → R :=
  fun i => (if i = j then 0 else x i) + (q i).eval₂ ρ (x j)

theorem eval₂_polynomialShear {R : Type w} [CommRing R] (ρ : k →+* R)
    (j : I) (q φ : I → k[X]) (x : R) :
    (fun i => (polynomialShear j q φ i).eval₂ ρ x) =
      polynomialShearValues ρ j q (fun i => (φ i).eval₂ ρ x) := by
  funext i
  by_cases hi : i = j <;>
    simp [polynomialShear, polynomialShearValues, hi, eval₂_comp]

/-- The inverse-shear formula works on all commutative algebras, including
nonreduced algebras and algebras in an independent universe. -/
theorem polynomialShearValues_inverse {R : Type w} [CommRing R] (ρ : k →+* R)
    (j : I) (a : k) (ha : a ≠ 0) (q : I → k[X])
    (hqj : q j = C a * X) (x : I → R) :
    polynomialShearValues ρ j q
      (polynomialShearValues ρ j (polynomialShearInverseCoordinates j a q) x) = x := by
  have hunit (z : R) : ρ a * (ρ a⁻¹ * z) = z := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  funext i
  by_cases hi : i = j
  · subst i
    simpa [polynomialShearValues, polynomialShearInverseCoordinates, hqj] using hunit (x j)
  · simp [polynomialShearValues, polynomialShearInverseCoordinates, hi, eval₂_comp]

theorem polynomialShearValues_inverse_shear {R : Type w} [CommRing R] (ρ : k →+* R)
    (j : I) (a : k) (ha : a ≠ 0) (q : I → k[X])
    (hqj : q j = C a * X) (x : I → R) :
    polynomialShearValues ρ j (polynomialShearInverseCoordinates j a q)
      (polynomialShearValues ρ j q x) = x := by
  have hunit (z : R) : ρ a⁻¹ * (ρ a * z) = z := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  funext i
  by_cases hi : i = j
  · subst i
    simpa [polynomialShearValues, polynomialShearInverseCoordinates, hqj] using hunit (x j)
  · simp [polynomialShearValues, polynomialShearInverseCoordinates, hi, hqj,
      eval₂_comp, hunit]


/-- Substitution by a triangular change preserves a separated additive row:
only its distinguished entry changes. -/
def polynomialShearRow [Fintype I] (j : I) (f q : I → k[X]) : I → k[X] :=
  fun i => if i = j then ∑ l, (f l).comp (q l) else f i

theorem polynomialShearRow_isAdditive [Fintype I] (j : I) (f q : I → k[X])
    (hf : ∀ i, IsAdditive (f i)) (hq : ∀ i, IsAdditive (q i)) :
    ∀ i, IsAdditive (polynomialShearRow j f q i) := by
  intro i
  by_cases hi : i = j
  · simpa [polynomialShearRow, hi] using
      IsAdditive.sum Finset.univ _ (fun l _ => (hf l).comp (hq l))
  · simpa [polynomialShearRow, hi] using hf i

/-- The row-transformation identity holds on every commutative coefficient
algebra, including nonreduced ones. -/
theorem sum_eval₂_polynomialShearValues [Fintype I]
    {R : Type w} [CommRing R] (ρ : k →+* R) (j : I) (f q : I → k[X])
    (hf : ∀ i, IsAdditive (f i)) (x : I → R) :
    (∑ i, (f i).eval₂ ρ (polynomialShearValues ρ j q x i)) =
      ∑ i, (polynomialShearRow j f q i).eval₂ ρ (x i) := by
  have hleft :
      (∑ i, (f i).eval₂ ρ (polynomialShearValues ρ j q x i)) =
        (∑ i, if i = j then 0 else (f i).eval₂ ρ (x i)) +
          (∑ i, (f i).comp (q i)).eval₂ ρ (x j) := by
    simp only [polynomialShearValues, (hf _).eval₂_add, eval₂_finsetSum,
      eval₂_comp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · simp [hi, eval₂_at_zero, (hf j).coeff_zero]
    · simp [hi]
  rw [hleft]
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := fun i => (polynomialShearRow j f q i).eval₂ ρ (x i)) (Finset.mem_univ j)]
  simp only [polynomialShearRow, ite_true]
  congr 1
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := fun i => if i = j then 0 else (f i).eval₂ ρ (x i)) (Finset.mem_univ j)]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [(Finset.mem_erase.mp hi).1]

section Actual

variable {n : ℕ}

/-- The triangular change on the points of every relative scheme test. -/
def polynomialShearPoints (j : Fin n) (q : Fin n → k[X])
    (hq : ∀ i, IsAdditive (q i)) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) →*
      (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) where
  toFun x := (VectorGroup.coordinates (CommRingCat.of k) n T).symm
    (Multiplicative.ofAdd (polynomialShearValues (AdditiveGroupQuotient.structureMap T)
      j q (VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd))
  map_one' := by
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    funext i
    simp only [MulEquiv.apply_symm_apply, map_one, toAdd_one, toAdd_ofAdd,
      polynomialShearValues, Pi.zero_apply]
    simp [eval₂_at_zero, (hq i).coeff_zero]
  map_mul' x y := by
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    funext i
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd,
      polynomialShearValues, Pi.add_apply, (hq i).eval₂_add]
    by_cases hi : i = j
    · simp [hi]
    · simp only [ite_eq_right hi]
      abel

@[simp]
theorem polynomialShearPoints_coord (j : Fin n) (q : Fin n → k[X])
    (hq : ∀ i, IsAdditive (q i)) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    (VectorGroup.coordinates (CommRingCat.of k) n T
      (polynomialShearPoints j q hq T x)).toAdd =
        polynomialShearValues (AdditiveGroupQuotient.structureMap T) j q
          (VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd := by
  simp only [polynomialShearPoints, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem polynomialShearPoints_natural (j : Fin n) (q : Fin n → k[X])
    (hq : ∀ i, IsAdditive (q i))
    {T W : Over (Spec (CommRingCat.of k))} (a : W ⟶ T)
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    polynomialShearPoints j q hq W (a ≫ x) = a ≫ polynomialShearPoints j q hq T x := by
  apply VectorGroup.points_ext
  intro i
  rw [polynomialShearPoints_coord, VectorGroup.coordinates_comp,
    VectorGroup.coordinates_comp]
  change (if i = j then 0 else
    a.left.appTop.hom ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd i)) +
    (q i).eval₂ (AdditiveGroupQuotient.structureMap W)
      (a.left.appTop.hom ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd j)) =
    a.left.appTop.hom _
  rw [polynomialShearPoints_coord]
  simp only [polynomialShearValues, map_add, Polynomial.hom_eval₂,
    AdditiveGroupQuotient.structureMap_comp]
  by_cases hi : i = j <;> simp [hi]

/-- The actual group-scheme homomorphism for an additive triangular change. -/
def polynomialShearHom (j : Fin n) (q : Fin n → k[X])
    (hq : ∀ i, IsAdditive (q i)) :
    VectorGroup.groupScheme (CommRingCat.of k) n ⟶
      VectorGroup.groupScheme (CommRingCat.of k) n :=
  homOfPoints (polynomialShearPoints j q hq) (polynomialShearPoints_natural j q hq)

@[simp]
theorem comp_polynomialShearHom (j : Fin n) (q : Fin n → k[X])
    (hq : ∀ i, IsAdditive (q i)) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    x ≫ (polynomialShearHom j q hq).hom.hom = polynomialShearPoints j q hq T x :=
  comp_homOfPoints _ _ T x

/-- A nonzero distinguished linear coefficient makes the triangular change an
actual vector-group isomorphism. -/
def polynomialShearIso (j : Fin n) (a : k) (ha : a ≠ 0)
    (q : Fin n → k[X]) (hqj : q j = C a * X) (hq : ∀ i, IsAdditive (q i)) :
    VectorGroup.groupScheme (CommRingCat.of k) n ≅
      VectorGroup.groupScheme (CommRingCat.of k) n where
  hom := polynomialShearHom j q hq
  inv := polynomialShearHom j (polynomialShearInverseCoordinates j a q)
    (polynomialShearInverseCoordinates_isAdditive j a q hq)
  hom_inv_id := by
    apply hom_ext_points
    intro T x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_polynomialShearHom,
      comp_polynomialShearHom, Grp.id_hom_hom, Category.comp_id]
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    rw [polynomialShearPoints_coord, polynomialShearPoints_coord]
    exact polynomialShearValues_inverse_shear _ j a ha q hqj _
  inv_hom_id := by
    apply hom_ext_points
    intro T x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_polynomialShearHom,
      comp_polynomialShearHom, Grp.id_hom_hom, Category.comp_id]
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    rw [polynomialShearPoints_coord, polynomialShearPoints_coord]
    exact polynomialShearValues_inverse _ j a ha q hqj _

/-- Substitution of an actual triangular homomorphism into an actual polynomial
row is the actual polynomial homomorphism with the transformed row. -/
theorem polynomialShearHom_comp_polynomialRow (j : Fin n) (f q : Fin n → k[X])
    (hf : ∀ i, IsAdditive (f i)) (hq : ∀ i, IsAdditive (q i)) :
    polynomialShearHom j q hq ≫ polynomialRow f hf =
      polynomialRow (polynomialShearRow j f q) (polynomialShearRow_isAdditive j f q hf hq) := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_polynomialShearHom,
    comp_polynomialRow, comp_polynomialRow]
  apply VectorGroup.points_ext
  intro i
  rw [polynomialRowPoints_coord, polynomialRowPoints_coord]
  simp_rw [polynomialShearPoints_coord]
  exact sum_eval₂_polynomialShearValues _ j f q hf _

/-- The row-transformation identity for the actual triangular isomorphism. -/
theorem polynomialShearIso_hom_comp_polynomialRow (j : Fin n) (a : k) (ha : a ≠ 0)
    (f q : Fin n → k[X]) (hqj : q j = C a * X)
    (hf : ∀ i, IsAdditive (f i)) (hq : ∀ i, IsAdditive (q i)) :
    (polynomialShearIso j a ha q hqj hq).hom ≫ polynomialRow f hf =
      polynomialRow (polynomialShearRow j f q) (polynomialShearRow_isAdditive j f q hf hq) :=
  polynomialShearHom_comp_polynomialRow j f q hf hq

end Actual

end Langlands.GroupScheme.Unipotent
