import Langlands.GroupScheme.Unipotent.AdditiveKernelGalois
import Langlands.GroupScheme.Rational.AdditiveGroupQuotient
import Langlands.GroupScheme.LinearKernelTowerSection

/-! # Actual closed additive curves from polynomial section and retraction identities -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

/-- Polynomial additivity can be evaluated along any coefficient homomorphism. -/
theorem OneDimensional.IsAdditive.eval₂_add {f : k[X]} (hf : IsAdditive f)
    {R : Type*} [CommRing R] (ρ : k →+* R) (x y : R) :
    f.eval₂ ρ (x + y) = f.eval₂ ρ x + f.eval₂ ρ y := by
  let := ρ.toAlgebra
  exact hf.aeval_add x y

/-- An additive tuple acts on every relative scheme test by evaluating its
coordinates at the coordinate of the one-dimensional vector group. -/
def polynomialCurvePoints (ψ : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i))
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) →*
      (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) where
  toFun x := (VectorGroup.coordinates (CommRingCat.of k) n T).symm
    (Multiplicative.ofAdd fun i => (ψ i).eval₂ (AdditiveGroupQuotient.structureMap T)
      ((VectorGroup.coordinates (CommRingCat.of k) 1 T x).toAdd 0))
  map_one' := by
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    funext i
    simp only [MulEquiv.apply_symm_apply, map_one, toAdd_one, toAdd_ofAdd, Pi.zero_apply]
    rw [eval₂_at_zero, (hψ i).coeff_zero, map_zero]
  map_mul' x y := by
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    apply Multiplicative.toAdd.injective
    funext i
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]
    exact (hψ i).eval₂_add _ _ _

@[simp]
theorem polynomialCurvePoints_coord (ψ : Fin n → k[X])
    (hψ : ∀ i, IsAdditive (ψ i)) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) (i : Fin n) :
    (VectorGroup.coordinates (CommRingCat.of k) n T
      (polynomialCurvePoints ψ hψ T x)).toAdd i =
        (ψ i).eval₂ (AdditiveGroupQuotient.structureMap T)
          ((VectorGroup.coordinates (CommRingCat.of k) 1 T x).toAdd 0) :=
by
  simp only [polynomialCurvePoints, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem polynomialCurvePoints_natural (ψ : Fin n → k[X])
    (hψ : ∀ i, IsAdditive (ψ i))
    {T W : Over (Spec (CommRingCat.of k))} (a : W ⟶ T)
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
    polynomialCurvePoints ψ hψ W (a ≫ x) = a ≫ polynomialCurvePoints ψ hψ T x := by
  apply VectorGroup.points_ext
  intro i
  rw [polynomialCurvePoints_coord, VectorGroup.coordinates_comp,
    VectorGroup.coordinates_comp]
  change (ψ i).eval₂ (AdditiveGroupQuotient.structureMap W)
    (a.left.appTop.hom ((VectorGroup.coordinates (CommRingCat.of k) 1 T x).toAdd 0)) =
      a.left.appTop.hom _
  rw [polynomialCurvePoints_coord, Polynomial.hom_eval₂,
    AdditiveGroupQuotient.structureMap_comp]

/-- The actual homomorphism defined by an additive polynomial tuple. -/
def polynomialCurve (ψ : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i)) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶
      VectorGroup.groupScheme (CommRingCat.of k) n :=
  homOfPoints (polynomialCurvePoints ψ hψ) (polynomialCurvePoints_natural ψ hψ)

@[simp]
theorem comp_polynomialCurve (ψ : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i))
    (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
    x ≫ (polynomialCurve ψ hψ).hom.hom = polynomialCurvePoints ψ hψ T x :=
  comp_homOfPoints _ _ T x

/-- A row of additive polynomials acts on every test scheme by summing the
coordinate evaluations. -/
def polynomialRowPoints (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) →*
      (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) where
  toFun x := (VectorGroup.coordinates (CommRingCat.of k) 1 T).symm
    (Multiplicative.ofAdd fun _ => ∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap T)
      ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd i))
  map_one' := by
    apply (VectorGroup.coordinates (CommRingCat.of k) 1 T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_one, toAdd_one, toAdd_ofAdd, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [eval₂_at_zero, (hf i).coeff_zero, map_zero]
  map_mul' x y := by
    apply (VectorGroup.coordinates (CommRingCat.of k) 1 T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]
    simp only [(fun i => (hf i).eval₂_add (AdditiveGroupQuotient.structureMap T)), Finset.sum_add_distrib]

@[simp]
theorem polynomialRowPoints_coord (f : Fin n → k[X])
    (hf : ∀ i, IsAdditive (f i)) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) (j : Fin 1) :
    (VectorGroup.coordinates (CommRingCat.of k) 1 T
      (polynomialRowPoints f hf T x)).toAdd j =
        ∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap T)
          ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd i) :=
by
  simp only [polynomialRowPoints, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem polynomialRowPoints_natural (f : Fin n → k[X])
    (hf : ∀ i, IsAdditive (f i))
    {T W : Over (Spec (CommRingCat.of k))} (a : W ⟶ T)
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    polynomialRowPoints f hf W (a ≫ x) = a ≫ polynomialRowPoints f hf T x := by
  apply VectorGroup.points_ext
  intro j
  rw [polynomialRowPoints_coord, VectorGroup.coordinates_comp,
    VectorGroup.coordinates_comp]
  change (∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap W)
    (a.left.appTop.hom ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd i))) =
      a.left.appTop.hom _
  rw [polynomialRowPoints_coord, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.hom_eval₂, AdditiveGroupQuotient.structureMap_comp]

/-- The actual homomorphism defined by a row of additive polynomials. -/
def polynomialRow (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    VectorGroup.groupScheme (CommRingCat.of k) n ⟶
      VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  homOfPoints (polynomialRowPoints f hf) (polynomialRowPoints_natural f hf)

@[simp]
theorem comp_polynomialRow (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    x ≫ (polynomialRow f hf).hom.hom = polynomialRowPoints f hf T x :=
  comp_homOfPoints _ _ T x

/-- The polynomial row identity is an identity of actual group-scheme maps. -/
theorem polynomialCurve_comp_polynomialRow_eq_id
    (ψ r : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i))
    (hr : ∀ i, IsAdditive (r i)) (hret : (∑ i, (r i).comp (ψ i)) = X) :
    polynomialCurve ψ hψ ≫ polynomialRow r hr = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_polynomialCurve,
    comp_polynomialRow, Grp.id_hom_hom, Category.comp_id]
  apply VectorGroup.points_ext
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rw [polynomialRowPoints_coord]
  simp_rw [polynomialCurvePoints_coord]
  let := (AdditiveGroupQuotient.structureMap T).toAlgebra
  change (∑ i, aeval (aeval ((VectorGroup.coordinates (CommRingCat.of k) 1 T x).toAdd 0)
    (ψ i)) (r i)) = _
  rw [sum_aeval_aeval, hret, aeval_X]

/-- The polynomial kernel identity vanishes as an actual group-scheme map. -/
theorem polynomialCurve_comp_polynomialRow_eq_zero
    (ψ f : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i))
    (hf : ∀ i, IsAdditive (f i)) (hrel : (∑ i, (f i).comp (ψ i)) = 0) :
    polynomialCurve ψ hψ ≫ polynomialRow f hf = 0 := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_polynomialCurve,
    comp_polynomialRow, Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
  apply VectorGroup.points_ext
  intro j
  rw [polynomialRowPoints_coord]
  simp_rw [polynomialCurvePoints_coord]
  simp only [map_one, toAdd_one, Pi.zero_apply]
  let := (AdditiveGroupQuotient.structureMap T).toAlgebra
  exact sum_aeval_aeval_eq_zero f ψ hrel _

/-- A polynomial retraction makes the actual additive curve a closed subgroup. -/
theorem polynomialCurve_isClosedSubgroup
    (ψ r : Fin n → k[X]) (hψ : ∀ i, IsAdditive (ψ i))
    (hr : ∀ i, IsAdditive (r i)) (hret : (∑ i, (r i).comp (ψ i)) = X) :
    IsClosedSubgroup (polynomialCurve ψ hψ) := by
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom := by
    change IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
    infer_instance
  exact LinearKernelTower.isClosedSubgroup_of_section (polynomialRow r hr)
    (polynomialCurve ψ hψ) (polynomialCurve_comp_polynomialRow_eq_id ψ r hψ hr hret)

/-- Factor an additive polynomial curve through the actual group-scheme kernel. -/
def polynomialKernelCurve
    (f ψ : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hψ : ∀ i, IsAdditive (ψ i)) (hrel : (∑ i, (f i).comp (ψ i)) = 0) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf) :=
  pullback.lift (polynomialCurve ψ hψ) 0
    (by simpa using polynomialCurve_comp_polynomialRow_eq_zero ψ f hψ hf hrel)

@[reassoc (attr := simp)]
theorem polynomialKernelCurve_comp_ι
    (f ψ : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hψ : ∀ i, IsAdditive (ψ i)) (hrel : (∑ i, (f i).comp (ψ i)) = 0) :
    polynomialKernelCurve f ψ hf hψ hrel ≫ kernelι (polynomialRow f hf) =
      polynomialCurve ψ hψ :=
  pullback.lift_fst _ _ _

/-- The kernel curve inherits the ambient polynomial retraction. -/
theorem polynomialKernelCurve_comp_retraction
    (f ψ r : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hψ : ∀ i, IsAdditive (ψ i)) (hr : ∀ i, IsAdditive (r i))
    (hrel : (∑ i, (f i).comp (ψ i)) = 0)
    (hret : (∑ i, (r i).comp (ψ i)) = X) :
    polynomialKernelCurve f ψ hf hψ hrel ≫
      (kernelι (polynomialRow f hf) ≫ polynomialRow r hr) = 𝟙 _ := by
  rw [← Category.assoc, polynomialKernelCurve_comp_ι,
    polynomialCurve_comp_polynomialRow_eq_id ψ r hψ hr hret]

/-- The factored curve is a closed immersion into the actual kernel. -/
theorem polynomialKernelCurve_isClosedSubgroup
    (f ψ r : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hψ : ∀ i, IsAdditive (ψ i)) (hr : ∀ i, IsAdditive (r i))
    (hrel : (∑ i, (f i).comp (ψ i)) = 0)
    (hret : (∑ i, (r i).comp (ψ i)) = X) :
    IsClosedSubgroup (polynomialKernelCurve f ψ hf hψ hrel) := by
  have hcurve : IsClosedSubgroup (polynomialCurve ψ hψ) :=
    polynomialCurve_isClosedSubgroup ψ r hψ hr hret
  change IsClosedImmersion (polynomialKernelCurve f ψ hf hψ hrel).hom.hom.left
  have he : (polynomialKernelCurve f ψ hf hψ hrel).hom.hom.left ≫
      (kernelι (polynomialRow f hf)).hom.hom.left = (polynomialCurve ψ hψ).hom.hom.left := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, polynomialKernelCurve_comp_ι]
  have : IsClosedImmersion ((polynomialKernelCurve f ψ hf hψ hrel).hom.hom.left ≫
      (kernelι (polynomialRow f hf)).hom.hom.left) := he.symm ▸ hcurve
  exact IsClosedImmersion.of_comp _ (kernelι (polynomialRow f hf)).hom.hom.left

/-- A split polynomial curve yields a closed one-dimensional vector subgroup of
an actual polynomial kernel, with an actual homomorphic retraction. -/
theorem HasSplitAdditiveKernelCurve.exists_closed_kernel_section
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (h : HasSplitAdditiveKernelCurve f) :
    ∃ s : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf),
      IsClosedSubgroup s ∧
        ∃ r : kernel (polynomialRow f hf) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
          s ≫ r = 𝟙 _ := by
  obtain ⟨ψ, r, hψ, hr, hrel, hret⟩ := h
  exact ⟨polynomialKernelCurve f ψ hf hψ hrel,
    polynomialKernelCurve_isClosedSubgroup f ψ r hf hψ hr hrel hret,
    kernelι (polynomialRow f hf) ≫ polynomialRow r hr,
    polynomialKernelCurve_comp_retraction f ψ r hf hψ hr hrel hret⟩

/-- Any nonconstant polynomial kernel curve gives an actual closed additive
subgroup and homomorphic retraction over its coefficient field. -/
theorem exists_closed_kernel_section_of_nonconstant
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : Fin n → k[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) :
    ∃ s : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf),
      IsClosedSubgroup s ∧
        ∃ r : kernel (polynomialRow f hf) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
          s ≫ r = 𝟙 _ :=
  (hasSplitAdditiveKernelCurve_of_nonconstant f hf φ hφ hrel).exists_closed_kernel_section f hf

/-- The same actual closed additive subgroup exists over the original field
when a nonconstant polynomial kernel curve exists over a Galois extension. -/
theorem exists_closed_kernel_section_of_nonconstant_galois
    {K : Type*} [Field K] [Algebra k K] [IsGalois k K]
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : Fin n → K[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0) :
    ∃ s : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf),
      IsClosedSubgroup s ∧
        ∃ r : kernel (polynomialRow f hf) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
          s ≫ r = 𝟙 _ :=
  (hasSplitAdditiveKernelCurve_of_nonconstant_galois f hf φ hφ hrel).exists_closed_kernel_section f hf

end Langlands.GroupScheme.Unipotent
