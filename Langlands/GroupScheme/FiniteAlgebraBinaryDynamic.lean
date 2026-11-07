import Langlands.GroupScheme.FiniteAlgebraBinaryRoots
import Langlands.GroupScheme.Dynamic.Basic

/-! # Actual cocharacters contracting binary elementary maps over finite algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot

section Matrices

variable {R S : Type u} [CommRing R] [Ring S] [Algebra R S]

/-- Select the upper family (`false`) or the lower family (`true`). -/
def elementaryMatrix (neg : Bool) (a : S) : Langlands.BinaryElementary.GL₂ S :=
  if neg then Langlands.BinaryElementary.lower a else Langlands.BinaryElementary.upper a

/-- The scalar diagonal has weights `(1,-1)` for the upper family and `(-1,1)` for the lower. -/
def contractingMatrixHom (neg : Bool) : Rˣ →* Langlands.BinaryElementary.GL₂ S where
  toFun t :=
    if neg then
      Langlands.BinaryElementary.diagonal
        (Units.map (algebraMap R S).toMonoidHom t⁻¹)
        (Units.map (algebraMap R S).toMonoidHom t)
    else
      Langlands.BinaryElementary.diagonal
        (Units.map (algebraMap R S).toMonoidHom t)
        (Units.map (algebraMap R S).toMonoidHom t⁻¹)
  map_one' := by
    cases neg <;> apply Units.ext <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Langlands.BinaryElementary.diagonal]
  map_mul' t v := by
    cases neg <;>
      simp only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev,
        mul_comm v⁻¹ t⁻¹, map_mul, Langlands.BinaryElementary.diagonal_mul]

/-- Arbitrary coefficient maps preserve both selected elementary families. -/
theorem map_elementaryMatrix {A B : Type u} [Ring A] [Ring B]
    (f : A →+* B) (neg : Bool) (a : A) :
    Units.map (RingHom.mapMatrix f).toMonoidHom (elementaryMatrix neg a) =
      elementaryMatrix neg (f a) := by
  cases neg
  · exact map_upper f a
  · exact map_lower f a

/-- The scalar diagonal commutes with change of commutative coefficient algebra. -/
theorem map_contractingMatrix {A B C E : Type u}
    [CommRing A] [CommRing B] [Ring C] [Ring E] [Algebra A C] [Algebra B E]
    (f : A →+* B) (g : C →+* E)
    (h : ∀ a, g (algebraMap A C a) = algebraMap B E (f a))
    (neg : Bool) (t : Aˣ) :
    Units.map (RingHom.mapMatrix g).toMonoidHom (contractingMatrixHom neg t) =
      contractingMatrixHom neg (Units.map f.toMonoidHom t) := by
  apply Units.ext
  ext i j
  cases neg <;> fin_cases i <;> fin_cases j <;>
    simp [contractingMatrixHom, Langlands.BinaryElementary.diagonal,
      RingHom.mapMatrix_apply, h]

/-- Conjugation multiplies the selected elementary parameter by the square of the scalar. -/
theorem contractingMatrix_conjugate (neg : Bool) (t : Rˣ) (a : S) :
    contractingMatrixHom neg t * elementaryMatrix neg a * (contractingMatrixHom neg t)⁻¹ =
      elementaryMatrix neg ((algebraMap R S (t : R)) ^ 2 * a) := by
  have hc : algebraMap R S (t : R) * a * algebraMap R S (t : R) =
      (algebraMap R S (t : R)) ^ 2 * a := by
    rw [mul_assoc, ← Algebra.commutes (t : R) a, ← mul_assoc, pow_two]
  cases neg
  · change Langlands.BinaryElementary.diagonal _ _ * Langlands.BinaryElementary.upper a *
        (Langlands.BinaryElementary.diagonal _ _)⁻¹ = _
    rw [Langlands.BinaryElementary.diagonal_conj_upper]
    simp only [← map_inv, inv_inv]
    change Langlands.BinaryElementary.upper (algebraMap R S (t : R) * a *
      algebraMap R S (t : R)) = _
    exact congrArg Langlands.BinaryElementary.upper hc
  · change Langlands.BinaryElementary.diagonal _ _ * Langlands.BinaryElementary.lower a *
        (Langlands.BinaryElementary.diagonal _ _)⁻¹ = _
    rw [Langlands.BinaryElementary.diagonal_conj_lower]
    simp only [← map_inv, inv_inv]
    change Langlands.BinaryElementary.lower (algebraMap R S (t : R) * a *
      algebraMap R S (t : R)) = _
    exact congrArg Langlands.BinaryElementary.lower hc

/-- The elementary unit with zero parameter is the identity, in either family. -/
theorem elementaryMatrix_zero (neg : Bool) : elementaryMatrix neg (0 : S) = 1 := by
  cases neg <;> apply Units.ext <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [elementaryMatrix, Langlands.BinaryElementary.upper, Langlands.BinaryElementary.lower]

end Matrices

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  {d n : ℕ} (bD : Module.Basis (Fin d) k D)
  (bA : Module.Basis (Fin n) k (Matrix (Fin 2) (Fin 2) D))

/-- The actual tensor coefficient algebra on a relative test scheme. -/
abbrev tensorAlgebra (T : Over (base k)) :=
  ((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D

/-- Pullback of actual tensor coefficients along a change of relative test. -/
def tensorMap {T T' : Over (base k)} (a : T' ⟶ T) :
    tensorAlgebra k D T →ₐ[k] tensorAlgebra k D T' :=
  Algebra.TensorProduct.map ((algΓ (CommRingCat.of k)).map a).unop.hom (AlgHom.id k D)

/-- The scalar sections enter the left tensor factor as central elements. -/
def includeSections (T : Over (base k)) : Γ(T.left, ⊤) →+* tensorAlgebra k D T :=
  (Algebra.TensorProduct.includeLeft :
    ((algΓ (CommRingCat.of k)).obj T).unop →ₐ[k] tensorAlgebra k D T).toRingHom

theorem tensorMap_includeSections {T T' : Over (base k)}
    (a : T' ⟶ T) (r : Γ(T.left, ⊤)) :
    tensorMap k D a (includeSections k D T r) =
      includeSections k D T' (a.left.appTop r) := by
  rfl

theorem tensorMap_comp {T T' T'' : Over (base k)}
    (a : T' ⟶ T) (b : T'' ⟶ T') (x : tensorAlgebra k D T) :
    tensorMap k D b (tensorMap k D a x) = tensorMap k D (b ≫ a) x := by
  simp only [tensorMap, Functor.map_comp, unop_comp]
  change ((Algebra.TensorProduct.map _ (AlgHom.id k D)).comp
    (Algebra.TensorProduct.map _ (AlgHom.id k D))) x = _
  rw [← Algebra.TensorProduct.map_comp]
  rfl

/-- Select the actual upper or lower elementary map. -/
def elementaryMap (neg : Bool) : additiveScheme k (d := d) ⟶ groupScheme bA :=
  if neg then lowerMap k D bD bA else upperMap k D bD bA

/-- The selected actual map has its expected elementary tensor matrix on every test. -/
theorem tensorMatrixEquiv_elementaryMap (neg : Bool) (T : Over (base k))
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (elementaryMap k D bD bA neg).hom.hom) =
      elementaryMatrix neg (tensorCoordinates k D bD T x).toAdd := by
  cases neg
  · exact tensorMatrixEquiv_upperMap k D bD bA T x
  · exact tensorMatrixEquiv_lowerMap k D bD bA T x

/-- The contracting scalar diagonal on every actual relative point group. -/
def cocharacterPoints (neg : Bool) (T : Over (base k)) :
    (T ⟶ (Gm (base k)).X) →* (T ⟶ (groupScheme bA).X) :=
  (MatrixPoints.tensorMatrixEquiv k D bA T).symm.toMonoidHom.comp
    ((contractingMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
      (S := tensorAlgebra k D T) neg).comp (Gm.pointsEquiv (base k) T).toMonoidHom)

/-- The diagonal point homomorphism has the stated scalar tensor entries. -/
theorem tensorMatrixEquiv_cocharacterPoints (neg : Bool) (T : Over (base k))
    (x : T ⟶ (Gm (base k)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T (cocharacterPoints k D bA neg T x) =
      contractingMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
        (S := tensorAlgebra k D T) neg
        (Gm.pointsEquiv (base k) T x) :=
  (MatrixPoints.tensorMatrixEquiv k D bA T).apply_symm_apply _

/-- The scalar diagonals are natural for every actual relative test pullback. -/
theorem cocharacterPoints_naturality (neg : Bool)
    {T T' : Over (base k)} (a : T' ⟶ T) (x : T ⟶ (Gm (base k)).X) :
    cocharacterPoints k D bA neg T' (a ≫ x) = a ≫ cocharacterPoints k D bA neg T x := by
  apply (MatrixPoints.tensorMatrixEquiv k D bA T').injective
  rw [MatrixPoints.tensorMatrixEquiv_naturality, tensorMatrixEquiv_cocharacterPoints,
    tensorMatrixEquiv_cocharacterPoints]
  erw [map_contractingMatrix
    (A := ((algΓ (CommRingCat.of k)).obj T).unop)
    (B := ((algΓ (CommRingCat.of k)).obj T').unop)
    ((algΓ (CommRingCat.of k)).map a).unop.hom.toRingHom
    (tensorMap k D a).toRingHom (tensorMap_includeSections k D a)]
  rw [Gm.pointsEquiv_naturality]
  rfl

/-- The actual ground-field cocharacter contracting the selected elementary family. -/
def cocharacter (neg : Bool) : (Gm (base k)).toGrp ⟶ groupScheme bA :=
  homOfPoints (cocharacterPoints k D bA neg) (cocharacterPoints_naturality k D bA neg)

/-- On every test the actual cocharacter has its prescribed scalar diagonal. -/
theorem tensorMatrixEquiv_cocharacter (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (Gm (base k)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (cocharacter k D bA neg).hom.hom) =
      contractingMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
        (S := tensorAlgebra k D T) neg
        (Gm.pointsEquiv (base k) T x) := by
  rw [cocharacter, comp_homOfPoints]
  exact tensorMatrixEquiv_cocharacterPoints k D bA neg T x

/-- The polynomial curve with elementary tensor parameter `s²a` on `T × A¹`. -/
def contraction (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    T ⊗ AffineLine.scheme (base k) ⟶ (groupScheme bA).X :=
  (MatrixPoints.tensorMatrixEquiv k D bA _).symm
    (elementaryMatrix neg
      ((includeSections k D _
          ((snd T (AffineLine.scheme (base k))).left.appTop
            (AffineLine.coord (base k)))) ^ 2 *
        tensorMap k D (fst T (AffineLine.scheme (base k))) (tensorCoordinates k D bD T x).toAdd))

/-- Pulling back the actual curve pulls back precisely its polynomial tensor parameter. -/
theorem tensorMatrixEquiv_comp_contraction (neg : Bool) {T T' : Over (base k)}
    (a : T' ⟶ T ⊗ AffineLine.scheme (base k))
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T' (a ≫ contraction k D bD bA neg x) =
      elementaryMatrix neg
        ((includeSections k D T'
            ((a ≫ snd T (AffineLine.scheme (base k))).left.appTop
              (AffineLine.coord (base k)))) ^ 2 *
          tensorMap k D (a ≫ fst T (AffineLine.scheme (base k)))
            (tensorCoordinates k D bD T x).toAdd) := by
  rw [MatrixPoints.tensorMatrixEquiv_naturality]
  simp only [contraction, MulEquiv.apply_symm_apply, map_elementaryMatrix]
  change elementaryMatrix neg (tensorMap k D a _) = _
  simp only [map_mul, map_pow, tensorMap_includeSections, tensorMap_comp,
    Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The actual elementary curve extends the cocharacter conjugation orbit on every test. -/
theorem contraction_isOrbitExtension (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    Dynamic.IsOrbitExtension (cocharacter k D bA neg)
      (x ≫ (elementaryMap k D bD bA neg).hom.hom) (contraction k D bD bA neg x) := by
  apply (MatrixPoints.tensorMatrixEquiv k D bA _).injective
  rw [tensorMatrixEquiv_comp_contraction]
  simp only [Dynamic.orbit, map_mul, map_inv, tensorMatrixEquiv_cocharacter]
  rw [MatrixPoints.tensorMatrixEquiv_naturality, tensorMatrixEquiv_elementaryMap,
    map_elementaryMatrix]
  erw [contractingMatrix_conjugate]
  congr 1
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]
  rfl

/-- The actual elementary curve is the identity at zero. -/
theorem contraction_evalZero (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    Dynamic.evalZero (contraction k D bD bA neg x) = 1 := by
  apply (MatrixPoints.tensorMatrixEquiv k D bA _).injective
  rw [Dynamic.evalZero, tensorMatrixEquiv_comp_contraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection,
    map_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, elementaryMatrix_zero]

/-- The entire actual upper or lower elementary image contracts under the corresponding cocharacter. -/
theorem elementary_range_le_dynamicUnipotent (neg : Bool) :
    SubgroupFunctor.range (elementaryMap k D bD bA neg) ≤
      Dynamic.unipotent (cocharacter k D bA neg) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact ⟨contraction k D bD bA neg x, contraction_isOrbitExtension k D bD bA neg x,
    contraction_evalZero k D bD bA neg x⟩

end Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot
