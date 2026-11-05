import Langlands.GroupScheme.Rational.InvariantCoordinateIntegral
import Langlands.GroupScheme.Rational.VectorExtensionDescent

/-! # Splitting vector extensions by invariant coordinate integration -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.CoordinateIntegration

variable {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]

/-- Tensor contraction commutes with a matrix over the coefficient algebra. -/
theorem contract_mulVec {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : Coord H →ₗ[k] k) {d : ℕ} (M : Matrix (Fin d) (Fin d) A)
    (x : Fin d → A ⊗[k] Coord H) :
    (fun j => contract H A ℓ
      (((M.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord H)) *ᵥ x) j)) =
      M *ᵥ (fun j => contract H A ℓ (x j)) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  change contract H A ℓ ((algebraMap A (A ⊗[k] Coord H) (M j l)) * x l) = _
  rw [← Algebra.smul_def, map_smul]
  rfl

/-- Tensor contraction commutes with the finite coordinate action of an actual
point over the coefficient algebra. -/
theorem coordinateAction_contract
    {G V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction G V) {d : ℕ} (c : Lie.FiniteCoordinates V d)
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : Coord H →ₗ[k] k) (t : Lie.AffinePoints G A)
    (x : Fin d → A ⊗[k] Coord H) :
    (fun j => contract H A ℓ
      (a.coordinateAction c (CommAlgCat.of k (A ⊗[k] Coord H))
        (Lie.affineMap G Algebra.TensorProduct.includeLeft t) x j)) =
      a.coordinateAction c (CommAlgCat.of k A) t
        (fun j => contract H A ℓ (x j)) := by
  let f : CommAlgCat.of k A ⟶ CommAlgCat.of k (A ⊗[k] Coord H) :=
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  have hm := a.coordinateMatrix_naturality c f t
  rw [← a.coordinateMatrix_mulVec, ← a.coordinateMatrix_mulVec]
  change (fun j => contract H A ℓ
    (((a.coordinateMatrix c _ (G.affinePointMap f t) :
      Matrix (Fin d) (Fin d) (A ⊗[k] Coord H)) *ᵥ x) j)) = _
  rw [hm]
  exact contract_mulVec H ℓ (a.coordinateMatrix c _ t : Matrix (Fin d) (Fin d) A) x

end Langlands.GroupScheme.CoordinateIntegration

namespace Langlands.GroupScheme.InvariantIntegralVectorExtension

open RelativeRoot CoordinateIntegration VectorExtensionDescent

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {H E V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (n : V ⟶ E) (q : E ⟶ H)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 H.X)
    [Mono n.hom.hom]

local notation "δ" => VectorExtensionDescent.defect n q hn s hs

omit [IsAffineHom H.X.hom] in
/-- Associativity in the extension gives the actual defect cocycle equation. -/
theorem defect_cocycle {T : Over (Spec (CommRingCat.of k))} (t r w : T ⟶ H.X) :
    δ t r * δ (t * r) w = (VectorExtensionDescent.action n q hn).act (t ≫ s) (δ r w) * δ t (r * w) := by
  apply (cancel_mono n.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp, action_act_comp, defect_comp, defect_comp,
    defect_comp, defect_comp, mul_assoc t r w]
  group

variable [IsAffineHom V.X.hom] {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (I : InvariantIntegral H)

variable {A : Type u} [CommRing A] [Algebra k A]

/-- Integrate the second argument of the actual regular section defect. -/
def averageVector (t : Lie.AffinePoints H A) : Fin d → A :=
  fun j => I.average ((vectorAffineCoordinates e (A ⊗[k] Coord H)
    (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t)
      (universalPoint H A))).toAdd j)

/-- The averaged defect as an actual point of the vector kernel. -/
def averagePoint (t : Lie.AffinePoints H A) : Lie.AffinePoints V A :=
  (vectorAffineCoordinates e A).symm
    (Multiplicative.ofAdd (averageVector n q hn s hs e I t))

local notation "β" => averageVector n q hn s hs e I
local notation "ρ" => averagePoint n q hn s hs e I

omit [Mono n.hom.hom] [IsAffineHom V.X.hom] in
theorem averagePoint_coordinates (t : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (ρ t)).toAdd = β t := by
  rw [averagePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [IsAffineHom H.X.hom] [Mono n.hom.hom] [IsAffineHom V.X.hom] in
theorem affineMap_defect {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t r : Lie.AffinePoints H A) :
    Lie.affineMap V f (δ t r) =
      δ (Lie.affineMap H f t) (Lie.affineMap H f r) :=
  comp_defect n q hn s hs _ t r

variable (he : IsLinearVectorCoordinates (VectorExtensionDescent.action n q hn) e)
include he

omit [IsAffineHom V.X.hom] in
/-- Left translation of the averaging variable leaves the average fixed. -/
theorem averageVector_translate (t r : Lie.AffinePoints H A) :
    (fun j => I.average ((vectorAffineCoordinates e (A ⊗[k] Coord H)
      (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t)
        (Lie.affineMap H Algebra.TensorProduct.includeLeft r *
          universalPoint H A))).toAdd j)) = β t := by
  rw [← leftTranslation_universalPoint, ← leftTranslation_constant H r t,
    ← affineMap_defect, he.1.vectorAffineCoordinates_naturality]
  funext j
  exact I.left_invariant A r _

omit [IsAffineHom V.X.hom] in
/-- The normalized average fixes every vector from the coefficient algebra. -/
theorem average_constant (x : Lie.AffinePoints V A) :
    (fun j => I.average ((vectorAffineCoordinates e (A ⊗[k] Coord H)
      (Lie.affineMap V Algebra.TensorProduct.includeLeft x)).toAdd j)) =
      (vectorAffineCoordinates e A x).toAdd := by
  rw [he.1.vectorAffineCoordinates_naturality]
  funext j
  exact I.average_includeLeft _

/-- Averaging commutes with the ambient conjugation by a constant point. -/
theorem average_act (h : Lie.AffinePoints E A)
    (x : Lie.AffinePoints V (A ⊗[k] Coord H)) :
    (fun j => I.average ((vectorAffineCoordinates e (A ⊗[k] Coord H)
      ((VectorExtensionDescent.action n q hn).act (Lie.affineMap E Algebra.TensorProduct.includeLeft h) x)).toAdd j)) =
      (vectorAffineCoordinates e A ((VectorExtensionDescent.action n q hn).act h ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd fun j => I.average
          ((vectorAffineCoordinates e (A ⊗[k] Coord H) x).toAdd j))))).toAdd := by
  have hx := he.coordinateAction_eq (CommAlgCat.of k (A ⊗[k] Coord H))
    (Lie.affineMap E Algebra.TensorProduct.includeLeft h)
    (vectorAffineCoordinates e (A ⊗[k] Coord H) x).toAdd
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hx
  rw [← hx, CoordinateIntegration.coordinateAction_contract, he.coordinateAction_eq]

/-- Averaging the cocycle equation produces a regular coboundary. -/
theorem defect_add_averageVector (t r : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) =
      (vectorAffineCoordinates e A ((VectorExtensionDescent.action n q hn).act (t ≫ s) (ρ r))).toAdd + β t := by
  have hc := congrArg (fun x : Lie.AffinePoints V (A ⊗[k] Coord H) =>
      fun j : Fin d => I.average ((vectorAffineCoordinates e (A ⊗[k] Coord H) x).toAdd j))
    (defect_cocycle n q hn s hs (Lie.affineMap H Algebra.TensorProduct.includeLeft t)
      (Lie.affineMap H Algebra.TensorProduct.includeLeft r) (universalPoint H A))
  simp only [map_mul, toAdd_mul] at hc
  have h1 : (fun j : Fin d => I.average
      ((vectorAffineCoordinates e (A ⊗[k] Coord H)
        (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t)
          (Lie.affineMap H Algebra.TensorProduct.includeLeft r))).toAdd j +
       (vectorAffineCoordinates e (A ⊗[k] Coord H)
        (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t *
            Lie.affineMap H Algebra.TensorProduct.includeLeft r)
          (universalPoint H A))).toAdd j)) =
      (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) := by
    rw [← affineMap_defect, ← map_mul]
    funext j
    rw [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·)
      (congrFun (average_constant n q hn e I he _) j) rfl
  have h2 : (fun j : Fin d => I.average
      ((vectorAffineCoordinates e (A ⊗[k] Coord H)
        ((VectorExtensionDescent.action n q hn).act (Lie.affineMap H Algebra.TensorProduct.includeLeft t ≫ s)
          (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft r)
            (universalPoint H A)))).toAdd j +
       (vectorAffineCoordinates e (A ⊗[k] Coord H)
        (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t)
          (Lie.affineMap H Algebra.TensorProduct.includeLeft r *
            universalPoint H A))).toAdd j)) =
      (vectorAffineCoordinates e A ((VectorExtensionDescent.action n q hn).act (t ≫ s) (ρ r))).toAdd + β t := by
    have hts : Lie.affineMap H Algebra.TensorProduct.includeLeft t ≫ s =
        Lie.affineMap E (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord H) (t ≫ s) := by
      simp only [Lie.affineMap_apply, Category.assoc]
    rw [hts]
    funext j
    rw [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·)
      (congrFun (average_act n q hn e I he _ _) j)
      (congrFun (averageVector_translate n q hn s hs e I he t r) j)
  rw [← h1, ← h2]
  exact hc

/-- The averaged defect is a correction in the actual vector group. -/
theorem averagePoint_mul (t r : Lie.AffinePoints H A) :
    ρ (t * r) = (δ t r)⁻¹ * (VectorExtensionDescent.action n q hn).act (t ≫ s) (ρ r) * ρ t := by
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, averagePoint_coordinates]
  exact (eq_neg_add_of_add_eq (defect_add_averageVector n q hn s hs e I he t r)).trans
    (add_assoc _ _ _).symm

omit [IsAffineHom V.X.hom] in
/-- Averaging the actual defect commutes with every map of coefficient algebras. -/
theorem averageVector_naturality {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    β (Lie.affineMap H f t) = fun j => f (β t j) := by
  have hd : δ (Lie.affineMap H Algebra.TensorProduct.includeLeft (Lie.affineMap H f t))
      (universalPoint H B) =
    Lie.affineMap V (tensorMap H f)
      (δ (Lie.affineMap H Algebra.TensorProduct.includeLeft t) (universalPoint H A)) := by
    rw [affineMap_defect, tensorMap_universalPoint]
    congr 1
    simp only [← Lie.affineMap_comp, tensorMap_includeLeft]
  funext j
  simp only [averageVector]
  rw [hd, he.1.vectorAffineCoordinates_naturality]
  exact contract_naturality H I.linearForm f _

omit [IsAffineHom V.X.hom] in
/-- The averaged defect is natural as an actual vector point. -/
theorem averagePoint_naturality {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    Lie.affineMap V f (ρ t) = ρ (Lie.affineMap H f t) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.1.vectorAffineCoordinates_naturality, averagePoint_coordinates,
    averagePoint_coordinates, averageVector_naturality n q hn s hs e I he]

/-- Correct the original scheme section on affine points. -/
def sectionPoint (t : Lie.AffinePoints H A) : Lie.AffinePoints E A :=
  (ρ t ≫ n.hom.hom)⁻¹ * (t ≫ s)

local notation "σ" => sectionPoint n q hn s hs e I

/-- The corrected affine section preserves products. -/
theorem sectionPoint_mul (t r : Lie.AffinePoints H A) : σ (t * r) = σ t * σ r := by
  simp only [sectionPoint]
  rw [averagePoint_mul n q hn s hs e I he, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, action_act_comp, defect_comp]
  group

omit [IsAffineHom V.X.hom] in
/-- The corrected section is natural on coefficient algebras. -/
theorem sectionPoint_naturality {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    Lie.affineMap E f (σ t) = σ (Lie.affineMap H f t) := by
  rw [sectionPoint, sectionPoint, map_mul, map_inv,
    ← averagePoint_naturality n q hn s hs e I he]
  simp only [Lie.affineMap_apply, Category.assoc]

/-- The corrected section as a morphism of actual schemes. -/
def sectionHom : H.X ⟶ E.X :=
  PointedCoordinateWeights.homOfAffinePoints fun _ _ _ t => σ t

omit [IsAffineHom V.X.hom] in
theorem comp_sectionHom (t : Lie.AffinePoints H A) :
    t ≫ sectionHom n q hn s hs e I = σ t :=
  PointedCoordinateWeights.comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => sectionPoint_naturality n q hn s hs e I he f v) t

/-- The corrected scheme section preserves products on every test scheme. -/
theorem sectionHom_mul {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ H.X) :
    (t * r) ≫ sectionHom n q hn s hs e I =
      (t ≫ sectionHom n q hn s hs e I) * (r ≫ sectionHom n q hn s hs e I) := by
  have hu : (fst H.X H.X * snd H.X H.X) ≫ sectionHom n q hn s hs e I =
      (fst H.X H.X ≫ sectionHom n q hn s hs e I) *
        (snd H.X H.X ≫ sectionHom n q hn s hs e I) := by
    apply PointedCoordinateWeights.affine_hom_ext
    intro A _ _ v
    simp only [← Category.assoc, MonObj.comp_mul, comp_sectionHom n q hn s hs e I he,
      sectionPoint_mul n q hn s hs e I he]
  have htr : t * r = lift t r ≫ (fst H.X H.X * snd H.X H.X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [htr, Category.assoc, hu, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

omit [IsAffineHom V.X.hom] in
/-- Correcting by a kernel point keeps the map a section of the quotient. -/
theorem sectionHom_comp : sectionHom n q hn s hs e I ≫ q.hom.hom = 𝟙 H.X := by
  have hnq : n.hom.hom ≫ q.hom.hom = 1 := by
    have hm : n.hom.hom ∈ (SubgroupFunctor.range n).carrier V.X :=
      SubgroupFunctor.mem_range.2 ⟨𝟙 V.X, Category.id_comp _⟩
    rw [hn, mem_range_kernelι_iff] at hm
    exact hm
  apply PointedCoordinateWeights.affine_hom_ext
  intro A _ _ t
  rw [← Category.assoc, comp_sectionHom n q hn s hs e I he, sectionPoint, MonObj.mul_comp,
    GrpObj.inv_comp, Category.assoc, Category.assoc, hs, hnq, MonObj.comp_one, inv_one,
    one_mul, Category.comp_id]

/-- An invariant coordinate integral splits every extension with the supplied
scheme section and full linear vector-kernel presentation. -/
def extensionSection : H ⟶ E :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ sectionHom n q hn s hs e I)
    (sectionHom_mul n q hn s hs e I he))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The averaged homomorphism splits the original quotient over the original field. -/
theorem extensionSection_comp : extensionSection n q hn s hs e I he ≫ q = 𝟙 H := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, extensionSection, comp_homOfPoints,
    MonoidHom.mk'_apply, Category.assoc, sectionHom_comp n q hn s hs e I he,
    Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

end Langlands.GroupScheme.InvariantIntegralVectorExtension
