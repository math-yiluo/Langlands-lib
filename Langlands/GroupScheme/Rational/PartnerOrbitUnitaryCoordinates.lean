import Langlands.GroupScheme.Rational.PartnerOrbitSpecialUnitary
import Langlands.GroupScheme.Rational.SimpleRootFiberCoordinates

/-! # Unitary coordinates on relative root groups from partnered orbits of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

open SpecialLinear SpecialLinear.BinaryPresentation

local notation "SL3" A => Matrix.SpecialLinearGroup (Fin 3) A

section Matrices

variable {K : Type*} [Field K]

/-- The diagonal entries `(λμ, μ, 1)`. -/
def diagConjLeft (l m : Kˣ) : Fin 3 → K := ![((l * m : Kˣ) : K), (m : K), 1]

/-- The diagonal entries `((λμ)⁻¹, μ⁻¹, 1)`. -/
def diagConjRight (l m : Kˣ) : Fin 3 → K := ![(((l * m)⁻¹ : Kˣ) : K), ((m⁻¹ : Kˣ) : K), 1]

theorem diagonal_diagConjLeft_mul_right (l m : Kˣ) :
    Matrix.diagonal (diagConjLeft l m) * Matrix.diagonal (diagConjRight l m) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext r
  fin_cases r <;> (simp [diagConjLeft, diagConjRight]; try field_simp)

theorem diagonal_diagConjRight_mul_left (l m : Kˣ) :
    Matrix.diagonal (diagConjRight l m) * Matrix.diagonal (diagConjLeft l m) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext r
  fin_cases r <;> (simp [diagConjLeft, diagConjRight]; try field_simp)

/-- Conjugation of ternary `SL` by the diagonal matrix `diag(λμ, μ, 1)`. -/
def diagConj (l m : Kˣ) : (SL3 K) →* (SL3 K) where
  toFun g := ⟨Matrix.diagonal (diagConjLeft l m) * (g : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (diagConjRight l m), by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul,
      diagonal_diagConjLeft_mul_right, Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (diagConjLeft l m) * 1 * Matrix.diagonal (diagConjRight l m) = 1
    rw [Matrix.mul_one, diagonal_diagConjLeft_mul_right]
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.diagonal (diagConjLeft l m) * ((g : Matrix (Fin 3) (Fin 3) K) * h) *
        Matrix.diagonal (diagConjRight l m) =
      Matrix.diagonal (diagConjLeft l m) * g * Matrix.diagonal (diagConjRight l m) *
        (Matrix.diagonal (diagConjLeft l m) * h * Matrix.diagonal (diagConjRight l m))
    have e := diagonal_diagConjRight_mul_left l m
    calc _ = Matrix.diagonal (diagConjLeft l m) * g *
          (Matrix.diagonal (diagConjRight l m) * Matrix.diagonal (diagConjLeft l m)) * h *
          Matrix.diagonal (diagConjRight l m) := by
          rw [e, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem diagConj_apply (l m : Kˣ) (g : SL3 K) (r s : Fin 3) :
    (diagConj l m g : Matrix (Fin 3) (Fin 3) K) r s =
      diagConjLeft l m r * (g : Matrix (Fin 3) (Fin 3) K) r s * diagConjRight l m s := by
  change (Matrix.diagonal (diagConjLeft l m) * (g : Matrix (Fin 3) (Fin 3) K) *
    Matrix.diagonal (diagConjRight l m)) r s = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diagConj_left_upper (l m : Kˣ) (t : K) :
    diagConj l m (TernaryPresentation.left (upper t)) =
      TernaryPresentation.left (upper ((l : K) * t)) := by
  ext r s
  rw [diagConj_apply]
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight, TernaryPresentation.leftMatrix,
      Matrix.SpecialLinearGroup.transvection_coe] <;> field_simp

theorem diagConj_left_lower (l m : Kˣ) (t : K) :
    diagConj l m (TernaryPresentation.left (lower t)) =
      TernaryPresentation.left (lower (((l⁻¹ : Kˣ) : K) * t)) := by
  ext r s
  rw [diagConj_apply]
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight, TernaryPresentation.leftMatrix,
      Matrix.SpecialLinearGroup.transvection_coe] <;> field_simp

theorem diagConj_right_upper (l m : Kˣ) (t : K) :
    diagConj l m (TernaryPresentation.right (upper t)) =
      TernaryPresentation.right (upper ((m : K) * t)) := by
  ext r s
  rw [diagConj_apply]
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight, TernaryPresentation.rightMatrix,
      Matrix.SpecialLinearGroup.transvection_coe]
  field_simp

theorem diagConj_right_lower (l m : Kˣ) (t : K) :
    diagConj l m (TernaryPresentation.right (lower t)) =
      TernaryPresentation.right (lower (((m⁻¹ : Kˣ) : K) * t)) := by
  ext r s
  rw [diagConj_apply]
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight, TernaryPresentation.rightMatrix,
      Matrix.SpecialLinearGroup.transvection_coe] <;> field_simp

end Matrices

section Parameters

variable {A : Type*} [CommRing A] {c : SU3Root.RingInvolution A}

/-- The upper unipotent ternary special linear matrix of quadratic root parameters. -/
def upperSL3 (q : SU3Root.Parameters c) : SL3 A :=
  ⟨SU3Root.Parameters.matrix q, SU3Root.Parameters.matrix_det q⟩

/-- The lower unipotent ternary special linear matrix of quadratic root parameters, the
conjugate of the upper one by the antidiagonal Weyl element. -/
def lowerSL3 (q : SU3Root.Parameters c) : SL3 A :=
  ⟨(SU3Root.oppositeEmbedding c q : Matrix (Fin 3) (Fin 3) A), by
    rw [SU3Root.oppositeEmbedding_val]; simp [Matrix.det_fin_three]⟩

theorem coe_upperSL3 (q : SU3Root.Parameters c) :
    (upperSL3 q : Matrix (Fin 3) (Fin 3) A) =
      !![1, q.first, q.second; 0, 1, c.bar q.first; 0, 0, 1] := rfl

theorem coe_lowerSL3 (q : SU3Root.Parameters c) :
    (lowerSL3 q : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -c.bar q.first, 1, 0; q.second, -q.first, 1] :=
  SU3Root.oppositeEmbedding_val c q

theorem upperSL3_mem_twistFixedSubgroup (q : SU3Root.Parameters c) :
    upperSL3 q ∈ SU3Root.twistFixedSubgroup c :=
  (SU3Root.mem_twistFixedSubgroup c _).mpr (SU3Root.Parameters.matrix_preservesForm q)

theorem lowerSL3_mem_twistFixedSubgroup (q : SU3Root.Parameters c) :
    lowerSL3 q ∈ SU3Root.twistFixedSubgroup c :=
  (SU3Root.mem_twistFixedSubgroup c _).mpr
    (SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c q).1

theorem fixedSpecialUnitaryEquiv_symm_embedding (q : SU3Root.Parameters c) :
    ((SU3Root.fixedSpecialUnitaryEquiv c).symm
      ⟨SU3Root.Parameters.embedding c q, SU3Root.embedding_mem_specialUnitarySubgroup c q⟩).1 =
      upperSL3 q := rfl

theorem fixedSpecialUnitaryEquiv_symm_opposite (q : SU3Root.Parameters c) :
    ((SU3Root.fixedSpecialUnitaryEquiv c).symm
      ⟨SU3Root.oppositeEmbedding c q,
        SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c q⟩).1 = lowerSL3 q := rfl

/-- Upper unipotent ternary special linear matrices. -/
def IsUpperSL3 (g : SL3 A) : Prop := SU3Root.IsUpperUnipotent (g : Matrix (Fin 3) (Fin 3) A)

/-- Lower unipotent ternary special linear matrices. -/
def IsLowerSL3 (g : SL3 A) : Prop :=
  SU3Root.IsUpperUnipotent (g : Matrix (Fin 3) (Fin 3) A).transpose

theorem isUpperUnipotent_map_iff {B : Type*} [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (M : Matrix (Fin 3) (Fin 3) A) :
    SU3Root.IsUpperUnipotent (M.map f) ↔ SU3Root.IsUpperUnipotent M := by
  unfold SU3Root.IsUpperUnipotent
  simp only [Matrix.map_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun r => hf (by rw [h1, map_one]), fun r s hrs => hf (by rw [h2 r s hrs, map_zero])⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun r => by rw [h1, map_one], fun r s hrs => by rw [h2 r s hrs, map_zero]⟩

theorem isUpperSL3_map_iff {B : Type*} [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (g : SL3 A) : IsUpperSL3 (Matrix.SpecialLinearGroup.map f g) ↔ IsUpperSL3 g := by
  unfold IsUpperSL3
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact isUpperUnipotent_map_iff f hf _

theorem isLowerSL3_map_iff {B : Type*} [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (g : SL3 A) : IsLowerSL3 (Matrix.SpecialLinearGroup.map f g) ↔ IsLowerSL3 g := by
  unfold IsLowerSL3
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← Matrix.transpose_map]
  exact isUpperUnipotent_map_iff f hf _

theorem isUpperSL3_upperSL3 (q : SU3Root.Parameters c) : IsUpperSL3 (upperSL3 q) :=
  SU3Root.Parameters.matrix_upperUnipotent q

theorem isLowerSL3_lowerSL3 (q : SU3Root.Parameters c) : IsLowerSL3 (lowerSL3 q) := by
  unfold IsLowerSL3
  rw [coe_lowerSL3]
  constructor
  · intro r
    fin_cases r <;> rfl
  · intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all

/-- An upper unipotent matrix fixed by the unitary twist has quadratic root coordinates. -/
theorem exists_upperSL3_eq {g : SL3 A} (hu : IsUpperSL3 g)
    (hg : g ∈ SU3Root.twistFixedSubgroup c) : ∃ q : SU3Root.Parameters c, upperSL3 q = g := by
  obtain ⟨q, hq⟩ := (SU3Root.Parameters.mem_range_embedding (c := c)
    (Matrix.SpecialLinearGroup.toGL g)).mpr ⟨hu, (SU3Root.mem_twistFixedSubgroup c g).mp hg⟩
  exact ⟨q, Subtype.ext (congrArg Units.val hq)⟩

theorem isUpperUnipotent_gram_mul_mul_gram {M : Matrix (Fin 3) (Fin 3) A}
    (hM : SU3Root.IsUpperUnipotent M.transpose) :
    SU3Root.IsUpperUnipotent (SU3Root.gram A * M * SU3Root.gram A) := by
  obtain ⟨hd, hl⟩ := hM
  have h00 : M 0 0 = 1 := hd 0
  have h11 : M 1 1 = 1 := hd 1
  have h22 : M 2 2 = 1 := hd 2
  have h01 : M 0 1 = 0 := hl 1 0 (by decide)
  have h02 : M 0 2 = 0 := hl 2 0 (by decide)
  have h12 : M 1 2 = 0 := hl 2 1 (by decide)
  constructor
  · intro r
    fin_cases r <;>
      simp [SU3Root.gram, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
        h00, h11, h22]
  · intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp_all [SU3Root.gram, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

/-- A lower unipotent matrix fixed by the unitary twist has opposite quadratic root
coordinates. -/
theorem exists_lowerSL3_eq {g : SL3 A} (hl : IsLowerSL3 g)
    (hg : g ∈ SU3Root.twistFixedSubgroup c) : ∃ q : SU3Root.Parameters c, lowerSL3 q = g := by
  have hW : SU3Root.weylElement * Matrix.SpecialLinearGroup.toGL g * SU3Root.weylElement ∈
      SU3Root.specialUnitarySubgroup c :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (SU3Root.weylElement_mem_specialUnitarySubgroup c)
      (SU3Root.fixedSpecialUnitaryEquiv c ⟨g, hg⟩).2)
      (SU3Root.weylElement_mem_specialUnitarySubgroup c)
  obtain ⟨q, hq⟩ := (SU3Root.Parameters.mem_range_embedding (c := c)
    (SU3Root.weylElement * Matrix.SpecialLinearGroup.toGL g * SU3Root.weylElement)).mpr
    ⟨isUpperUnipotent_gram_mul_mul_gram hl, hW.1⟩
  refine ⟨q, Subtype.ext ?_⟩
  change ((SU3Root.oppositeEmbedding c q : Matrix.GeneralLinearGroup (Fin 3) A) :
    Matrix (Fin 3) (Fin 3) A) = g
  simp only [SU3Root.oppositeEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, SU3Root.weylElement_inv]
  rw [hq]
  have e : SU3Root.weylElement * (SU3Root.weylElement * Matrix.SpecialLinearGroup.toGL g *
      SU3Root.weylElement) * SU3Root.weylElement = Matrix.SpecialLinearGroup.toGL g := by
    simp only [← mul_assoc, SU3Root.weylElement_mul_self, one_mul]
    rw [mul_assoc, SU3Root.weylElement_mul_self, mul_one]
  rw [e]
  rfl

theorem upperSL3_injective : Function.Injective (upperSL3 (c := c)) := by
  intro q q' h
  have h' := congrArg (fun g : SL3 A => (g : Matrix (Fin 3) (Fin 3) A)) h
  simp only [coe_upperSL3] at h'
  apply SU3Root.Parameters.ext
  · simpa using congrFun (congrFun h' 0) 1
  · simpa using congrFun (congrFun h' 0) 2

theorem lowerSL3_injective : Function.Injective (lowerSL3 (c := c)) := by
  intro q q' h
  have h' := congrArg (fun g : SL3 A => (g : Matrix (Fin 3) (Fin 3) A)) h
  simp only [coe_lowerSL3] at h'
  apply SU3Root.Parameters.ext
  · simpa using congrFun (congrFun h' 2) 1
  · simpa using congrFun (congrFun h' 2) 0

/-- Upper unipotent ternary matrices whose two simple-root entries vanish. -/
def IsCentralUpperSL3 (g : SL3 A) : Prop :=
  IsUpperSL3 g ∧ (g : Matrix (Fin 3) (Fin 3) A) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) A) 1 2 = 0

/-- Lower unipotent ternary matrices whose two simple-root entries vanish. -/
def IsCentralLowerSL3 (g : SL3 A) : Prop :=
  IsLowerSL3 g ∧ (g : Matrix (Fin 3) (Fin 3) A) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) A) 2 1 = 0

theorem isCentralUpperSL3_map_iff {B : Type*} [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (g : SL3 A) :
    IsCentralUpperSL3 (Matrix.SpecialLinearGroup.map f g) ↔ IsCentralUpperSL3 g := by
  unfold IsCentralUpperSL3
  rw [isUpperSL3_map_iff f hf]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    map_eq_zero_iff f hf]

theorem isCentralLowerSL3_map_iff {B : Type*} [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (g : SL3 A) :
    IsCentralLowerSL3 (Matrix.SpecialLinearGroup.map f g) ↔ IsCentralLowerSL3 g := by
  unfold IsCentralLowerSL3
  rw [isLowerSL3_map_iff f hf]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    map_eq_zero_iff f hf]

theorem isCentralUpperSL3_upperSL3_iff (q : SU3Root.Parameters c) :
    IsCentralUpperSL3 (upperSL3 q) ↔ q ∈ SU3Root.Parameters.central c := by
  rw [SU3Root.Parameters.mem_central]
  refine ⟨fun h => ?_, fun h => ⟨isUpperSL3_upperSL3 q, ?_, ?_⟩⟩
  · simpa [coe_upperSL3] using h.2.1
  · simp [coe_upperSL3, h]
  · simp [coe_upperSL3, h]

theorem isCentralLowerSL3_lowerSL3_iff (q : SU3Root.Parameters c) :
    IsCentralLowerSL3 (lowerSL3 q) ↔ q ∈ SU3Root.Parameters.central c := by
  rw [SU3Root.Parameters.mem_central]
  refine ⟨fun h => ?_, fun h => ⟨isLowerSL3_lowerSL3 q, ?_, ?_⟩⟩
  · simpa [coe_lowerSL3] using h.2.2
  · simp [coe_lowerSL3, h]
  · simp [coe_lowerSL3, h]

variable (c) in
/-- The upper root parameters as special unitary matrices. -/
def upperUnitary : SU3Root.Parameters c →* SU3Root.specialUnitarySubgroup c :=
  (SU3Root.Parameters.embedding c).codRestrict _ (SU3Root.embedding_mem_specialUnitarySubgroup c)

variable (c) in
/-- The lower root parameters as special unitary matrices. -/
def lowerUnitary : SU3Root.Parameters c →* SU3Root.specialUnitarySubgroup c :=
  (SU3Root.oppositeEmbedding c).codRestrict _
    (SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c)

theorem fixedSpecialUnitaryEquiv_symm_upperUnitary (q : SU3Root.Parameters c) :
    ((SU3Root.fixedSpecialUnitaryEquiv c).symm (upperUnitary c q)).1 = upperSL3 q := rfl

theorem fixedSpecialUnitaryEquiv_symm_lowerUnitary (q : SU3Root.Parameters c) :
    ((SU3Root.fixedSpecialUnitaryEquiv c).symm (lowerUnitary c q)).1 = lowerSL3 q := rfl

end Parameters

section ParameterScaling

variable {K : Type*} [Field K] {L : Type*} [CommRing L] {c : SU3Root.RingInvolution L}

/-- Diagonal conjugation of the image of an upper matrix is the image of the scaled
parameters, when the diagonal values are the images of a scalar and its conjugate. -/
theorem diagConj_map_upperSL3 (f : L →+* K) (q : SU3Root.Parameters c) (y : L) (l m : Kˣ)
    (hl : (l : K) = f y) (hm : (m : K) = f (c.bar y)) :
    diagConj l m (Matrix.SpecialLinearGroup.map f (upperSL3 q)) =
      Matrix.SpecialLinearGroup.map f (upperSL3 (SU3Root.Parameters.scale y q)) := by
  ext r s
  rw [diagConj_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    coe_upperSL3, coe_upperSL3]
  have hy : f y ≠ 0 := hl ▸ l.ne_zero
  have hy' : f (c.bar y) ≠ 0 := hm ▸ m.ne_zero
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight, hl, hm] <;> field_simp

/-- Diagonal conjugation of the image of a lower matrix is the image of the scaled
parameters, when the inverse diagonal values are the images of a conjugate scalar and the
scalar. -/
theorem diagConj_map_lowerSL3 (f : L →+* K) (q : SU3Root.Parameters c) (y : L) (l m : Kˣ)
    (hl : ((l⁻¹ : Kˣ) : K) = f (c.bar y)) (hm : ((m⁻¹ : Kˣ) : K) = f y) :
    diagConj l m (Matrix.SpecialLinearGroup.map f (lowerSL3 q)) =
      Matrix.SpecialLinearGroup.map f (lowerSL3 (SU3Root.Parameters.scale y q)) := by
  ext r s
  rw [diagConj_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    coe_lowerSL3, coe_lowerSL3]
  simp only [Units.val_inv_eq_inv_val] at hl hm
  fin_cases r <;> fin_cases s <;>
    simp [diagConjLeft, diagConjRight] <;> (try field_simp) <;>
    (try simp [← hl, ← hm])
  all_goals field_simp

end ParameterScaling

/-- An injective coefficient map gives an injective map of ternary special linear groups. -/
theorem specialLinearMap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map f : (SL3 A) →* (SL3 B)) := by
  intro M N h
  ext r s
  have := congrArg (fun g : SL3 B => (g : Matrix (Fin 3) (Fin 3) B) r s) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact hf this

section Split

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
  (x : p.NormalizedSimpleRootParametrizations)

/-- The rational value of a simple root at a rational point of the split torus. -/
def rootValue (w : rationalPoints p.torus.toGrp) (a : p.base.support) : kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
    (p.rootDatum.root a)) w

theorem rationalCharacterEval_neg_root (w : rationalPoints p.torus.toGrp) (a : p.base.support) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
      (-p.rootDatum.root a)) w = (rootValue w a)⁻¹ := by
  rw [map_neg, rationalCharacterEval_neg]
  rfl

theorem conj_rootSL2_upper (w : rationalPoints p.torus.toGrp) (a : p.base.support) (t : k) :
    rationalPoints.map p.inclusion w * rootSL2 x a (upper t) *
        (rationalPoints.map p.inclusion w)⁻¹ =
      rootSL2 x a (upper ((rootValue w a : k) * t)) := by
  rw [rootSL2_upper, rootSL2_upper]
  exact (x a).linked.conj_xpPoint w t

theorem conj_rootSL2_lower (w : rationalPoints p.torus.toGrp) (a : p.base.support) (t : k) :
    rationalPoints.map p.inclusion w * rootSL2 x a (lower t) *
        (rationalPoints.map p.inclusion w)⁻¹ =
      rootSL2 x a (lower ((((rootValue w a)⁻¹ : kˣ) : k) * t)) := by
  rw [rootSL2_lower, rootSL2_lower, ← rationalCharacterEval_neg_root]
  exact (x a).linked.conj_xmPoint w t

/-- Rational points of the split torus act on the ternary homomorphism of a pair of simple
roots through diagonal conjugation by the values of the two roots. -/
theorem conj_pairSL3 {a b : p.base.support} (hab : p.rootDatum.pairing a b = -1)
    (hba : p.rootDatum.pairing b a = -1) (w : rationalPoints p.torus.toGrp) (g : SL3 k) :
    rationalPoints.map p.inclusion w * pairSL3 hAdj x a b g *
        (rationalPoints.map p.inclusion w)⁻¹ =
      pairSL3 hAdj x a b (diagConj (rootValue w a) (rootValue w b) g) := by
  have h : (MulAut.conj (rationalPoints.map p.inclusion w)).toMonoidHom.comp
      (pairSL3 hAdj x a b) =
      (pairSL3 hAdj x a b).comp (diagConj (rootValue w a) (rootValue w b)) := by
    apply TernaryPresentation.hom_ext
    · apply BinaryPresentation.hom_ext
      · intro t
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [pairSL3_left hAdj x hab hba, diagConj_left_upper, pairSL3_left hAdj x hab hba]
        exact conj_rootSL2_upper x w a t
      · intro t
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [pairSL3_left hAdj x hab hba, diagConj_left_lower, pairSL3_left hAdj x hab hba]
        exact conj_rootSL2_lower x w a t
    · apply BinaryPresentation.hom_ext
      · intro t
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [pairSL3_right hAdj x hab hba, diagConj_right_upper, pairSL3_right hAdj x hab hba]
        exact conj_rootSL2_upper x w b t
      · intro t
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [pairSL3_right hAdj x hab hba, diagConj_right_lower, pairSL3_right hAdj x hab hba]
        exact conj_rootSL2_lower x w b t
  exact DFunLike.congr_fun h g

/-- Rational points of the split torus act on pair-orbit products through diagonal
conjugation of every factor. -/
theorem PartnerData.conj_pairOrbitSL3 {O : Set p.base.support} (D : PartnerData O)
    (w : rationalPoints p.torus.toGrp) (h : p.base.support → SL3 k) :
    rationalPoints.map p.inclusion w * D.pairOrbitSL3 hAdj x h *
        (rationalPoints.map p.inclusion w)⁻¹ =
      D.pairOrbitSL3 hAdj x
        (fun a => diagConj (rootValue w a) (rootValue w (D.partner a)) (h a)) := by
  change MulAut.conj (rationalPoints.map p.inclusion w) (D.pairOrbitSL3 hAdj x h) = _
  rw [PartnerData.pairOrbitSL3_apply]
  refine (Finset.map_noncommProd _ _ _ (MulAut.conj (rationalPoints.map p.inclusion w))).trans ?_
  have hval : ∀ r : D.orientation,
      MulAut.conj (rationalPoints.map p.inclusion w) (pairSL3 hAdj x r (D.partner r) (h r)) =
        pairSL3 hAdj x r (D.partner r)
          (diagConj (rootValue w r) (rootValue w (D.partner r)) (h r)) := fun r =>
    conj_pairSL3 hAdj x (D.pairing r (D.mem_of_mem_orientation r.2)).1
      (D.pairing r (D.mem_of_mem_orientation r.2)).2 w (h r)
  simp only [hval]
  rfl

end Split

section Galois

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance partnerOrbitUnitaryCoordinatesIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
    (p : Langlands.GroupScheme.SplitPinning
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hρpair : ∀ (σ : K ≃ₐ[k] K) (a b : p.base.support),
      p.rootDatum.pairing (ρ σ a) (ρ σ b) = p.rootDatum.pairing a b)
    {O : Set p.base.support} (D : PartnerData O)
    (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hπρ : ∀ (σ : K ≃ₐ[k] K), ∀ a ∈ O, D.partner (ρ σ a) = ρ σ (D.partner a))

section Transport

/-- The Galois transport of a family of ternary matrices on the simple roots. -/
def galoisPair (σ : K ≃ₐ[k] K) (h : p.base.support → SL3 K) : p.base.support → SL3 K :=
  fun a => Matrix.SpecialLinearGroup.map σ.toRingHom (h ((ρ σ).symm a))

theorem galoisPair_apply (σ : K ≃ₐ[k] K) (h : p.base.support → SL3 K) (a : p.base.support) :
    galoisPair k K p (ρ := ρ) σ h (ρ σ a) = Matrix.SpecialLinearGroup.map σ.toRingHom (h a) := by
  simp [galoisPair]

include hOs hπρ in
/-- The Galois transport of a pair family is a pair family. -/
theorem isPairFamily_galoisPair (σ : K ≃ₐ[k] K) {h : p.base.support → SL3 K}
    (hh : D.IsPairFamily h) : D.IsPairFamily (galoisPair k K p (ρ := ρ) σ h) := by
  intro a ha
  have ha' : (ρ σ).symm a ∈ O := (hOs σ _).mpr (by rwa [Equiv.apply_symm_apply])
  have hp : (ρ σ).symm (D.partner a) = D.partner ((ρ σ).symm a) := by
    rw [Equiv.symm_apply_eq, ← hπρ σ _ ha', Equiv.apply_symm_apply]
  simp only [galoisPair]
  rw [hp, hh _ ha', TernaryPresentation.map_outer]

include hT hx hroot hρpair hOs hπρ in
/-- Conjugating the coefficients of the product of a pair family gives the product of its
Galois transport. -/
theorem rationalConjugate_pairOrbitSL3 {h : p.base.support → SL3 K} (hh : D.IsPairFamily h)
    (σ : K ≃ₐ[k] K) :
    rationalConjugate k K G σ (D.pairOrbitSL3 hAdj x h) =
      D.pairOrbitSL3 hAdj x (galoisPair k K p (ρ := ρ) σ h) := by
  have hh' := isPairFamily_galoisPair k K p D hOs hπρ σ hh
  let e : D.orientation ≃ D.orientation := Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (normalize_action_injective k K p D hOs hπρ σ))
  have hval : ∀ r : D.orientation,
      rationalConjugate k K G σ (pairSL3 hAdj x r (D.partner r) (h r)) =
        pairSL3 hAdj x (e r) (D.partner (e r)) (galoisPair k K p (ρ := ρ) σ h (e r)) := by
    intro r
    have hrO := D.mem_of_mem_orientation r.2
    rw [pairSL3_rationalConjugate k K i hAdj p eT hT x hx hroot hρpair σ (D.pairing r hrO).1
      (D.pairing r hrO).2, ← galoisPair_apply k K p (ρ := ρ) σ h, ← hπρ σ r hrO]
    exact (D.pairSL3_normalize_eq hAdj x hh' ((hOs σ r).mp hrO)).symm
  rw [PartnerData.pairOrbitSL3_apply, PartnerData.pairOrbitSL3_apply, Finset.map_noncommProd]
  simp only [hval]
  exact noncommProd_univ_equiv e
    (fun r : D.orientation =>
      pairSL3 hAdj x r (D.partner r) (galoisPair k K p (ρ := ρ) σ h r)) _ _

include hT hx hroot hρpair hOs hπρ in
/-- If the scalar extension of a rational point is the product of a pair family satisfying a
Galois-stable condition under which pair families are determined by their products, then the
family is Galois equivariant on `O`. -/
theorem map_eq_of_rationalExtend_eq (P : (SL3 K) → Prop)
    (hP : ∀ (σ : K ≃ₐ[k] K) (g : SL3 K), P g → P (Matrix.SpecialLinearGroup.map σ.toRingHom g))
    (huniq : ∀ h h' : p.base.support → SL3 K, (∀ a ∈ O, P (h a)) → (∀ a ∈ O, P (h' a)) →
      D.IsPairFamily h → D.IsPairFamily h' →
      D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h' → ∀ a ∈ O, h a = h' a)
    {g₀ : rationalPoints G} {h : p.base.support → SL3 K} (hPh : ∀ a ∈ O, P (h a))
    (hh : D.IsPairFamily h) (hg₀ : rationalExtend k K G g₀ = D.pairOrbitSL3 hAdj x h)
    (σ : K ≃ₐ[k] K) :
    ∀ a ∈ O, h (ρ σ a) = Matrix.SpecialLinearGroup.map σ.toRingHom (h a) := by
  intro a ha
  have h1 : D.pairOrbitSL3 hAdj x (galoisPair k K p (ρ := ρ) σ h) = D.pairOrbitSL3 hAdj x h := by
    rw [← rationalConjugate_pairOrbitSL3 k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ hh σ,
      ← hg₀, rationalConjugate_rationalExtend]
  have hP' : ∀ b ∈ O, P (galoisPair k K p (ρ := ρ) σ h b) := fun b hb =>
    hP σ _ (hPh _ ((hOs σ _).mpr (by rwa [Equiv.apply_symm_apply])))
  have h2 := huniq _ _ hP' hPh (isPairFamily_galoisPair k K p D hOs hπρ σ hh) hh h1 (ρ σ a)
    ((hOs σ a).mp ha)
  rw [galoisPair_apply] at h2
  exact h2.symm

end Transport

section Field

variable {L : Type u} [Field L] [Algebra k L] (τ : p.base.support → (L →ₐ[k] K))
  (hτ : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → τ (ρ σ a) = σ.toAlgHom.comp (τ a))
  (c : SU3Root.RingInvolution L)
  (hτc : ∀ a ∈ O, ∀ y : L, τ (D.partner a) y = τ a (c.bar y))

include hτc in
theorem map_map_bar {a : p.base.support} (ha : a ∈ O) (g : SL3 L) :
    Matrix.SpecialLinearGroup.map (τ a).toRingHom
        (Matrix.SpecialLinearGroup.map c.bar.toRingHom g) =
      Matrix.SpecialLinearGroup.map (τ (D.partner a)).toRingHom g := by
  ext r s
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hτc a ha]

include hτc in
/-- The embedding coordinates of a twist-fixed matrix form a pair family. -/
theorem isPairFamily_map {g : SL3 L} (hg : g ∈ SU3Root.twistFixedSubgroup c) :
    D.IsPairFamily (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom g) := by
  intro a ha
  show Matrix.SpecialLinearGroup.map (τ (D.partner a)).toRingHom g =
    TernaryPresentation.outer (Matrix.SpecialLinearGroup.map (τ a).toRingHom g)
  rw [← TernaryPresentation.map_outer,
    TernaryPresentation.outer_eq_map_of_mem_twistFixedSubgroup c g hg,
    map_map_bar k K p D τ c hτc ha]

include hτc in
/-- A Galois equivariant pair family on `O` comes from a single twist-fixed matrix over `L`,
when Galois equivariant families of scalars on `O` come from `L`. -/
theorem exists_twistFixed_map_eq
    (hfam : ∀ e : p.base.support → K,
      (∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → e (ρ σ a) = σ (e a)) →
        ∃ t : L, ∀ a ∈ O, e a = τ a t)
    {a₀ : p.base.support} (ha₀ : a₀ ∈ O) {h : p.base.support → SL3 K}
    (hfix : ∀ (σ : K ≃ₐ[k] K), ∀ a ∈ O,
      h (ρ σ a) = Matrix.SpecialLinearGroup.map σ.toRingHom (h a))
    (hh : D.IsPairFamily h) :
    ∃ g : SL3 L, g ∈ SU3Root.twistFixedSubgroup c ∧
      ∀ a ∈ O, Matrix.SpecialLinearGroup.map (τ a).toRingHom g = h a := by
  have hent : ∀ r s : Fin 3, ∃ t : L, ∀ a ∈ O,
      (h a : Matrix (Fin 3) (Fin 3) K) r s = τ a t := by
    intro r s
    refine hfam (fun a => (h a : Matrix (Fin 3) (Fin 3) K) r s) (fun σ a ha => ?_)
    simp only [hfix σ a ha, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rfl
  choose t ht using hent
  have hmap : ∀ a ∈ O, (Matrix.of t).map (τ a).toRingHom = (h a : Matrix (Fin 3) (Fin 3) K) := by
    intro a ha
    ext r s
    exact (ht r s a ha).symm
  have hdet : (Matrix.of t).det = 1 := by
    apply (τ a₀).toRingHom.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap a₀ ha₀, (h a₀).2, map_one]
  let g : SL3 L := ⟨Matrix.of t, hdet⟩
  have hg : ∀ a ∈ O, Matrix.SpecialLinearGroup.map (τ a).toRingHom g = h a := fun a ha =>
    Subtype.ext (hmap a ha)
  refine ⟨g, ?_, hg⟩
  change SU3Root.unitaryTwist c g = g
  rw [TernaryPresentation.unitaryTwist_eq_outer_map]
  apply specialLinearMap_injective (τ a₀).toRingHom (τ a₀).toRingHom.injective
  rw [TernaryPresentation.map_outer, map_map_bar k K p D τ c hτc ha₀, hg _ (D.mem a₀ ha₀),
    hh a₀ ha₀, TernaryPresentation.outer_outer, hg a₀ ha₀]

include hT hx hroot hρpair hOs hπρ hτc in
/-- Descent of a pair family of scalar-extended points: if the scalar extension of a rational
point is the product of a pair family satisfying a Galois-stable condition which determines
pair families from their products, the family comes from a twist-fixed matrix over `L`. -/
theorem exists_twistFixed_of_rationalExtend (P : (SL3 K) → Prop)
    (hP : ∀ (σ : K ≃ₐ[k] K) (g : SL3 K), P g → P (Matrix.SpecialLinearGroup.map σ.toRingHom g))
    (huniq : ∀ h h' : p.base.support → SL3 K, (∀ a ∈ O, P (h a)) → (∀ a ∈ O, P (h' a)) →
      D.IsPairFamily h → D.IsPairFamily h' →
      D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h' → ∀ a ∈ O, h a = h' a)
    (hfam : ∀ e : p.base.support → K,
      (∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → e (ρ σ a) = σ (e a)) →
        ∃ t : L, ∀ a ∈ O, e a = τ a t)
    {a₀ : p.base.support} (ha₀ : a₀ ∈ O)
    {g₀ : rationalPoints G} {h : p.base.support → SL3 K} (hPh : ∀ a ∈ O, P (h a))
    (hh : D.IsPairFamily h) (hg₀ : rationalExtend k K G g₀ = D.pairOrbitSL3 hAdj x h) :
    ∃ g : SL3 L, g ∈ SU3Root.twistFixedSubgroup c ∧
      ∀ a ∈ O, Matrix.SpecialLinearGroup.map (τ a).toRingHom g = h a :=
  exists_twistFixed_map_eq k K p D τ c hτc hfam ha₀
    (fun σ => map_eq_of_rationalExtend_eq k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ P hP
      huniq hPh hh hg₀ σ) hh

variable [FiniteDimensional k K] [IsGalois k K]

set_option hygiene false in
local notation "URho" => unitaryRho k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc

theorem rationalExtend_unitaryRho_upper (q : SU3Root.Parameters c) :
    rationalExtend k K G (URho (upperUnitary c q)) =
      D.pairOrbitSL3 hAdj x (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom (upperSL3 q)) :=
  rationalExtend_unitaryRho k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc _

theorem rationalExtend_unitaryRho_lower (q : SU3Root.Parameters c) :
    rationalExtend k K G (URho (lowerUnitary c q)) =
      D.pairOrbitSL3 hAdj x (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom (lowerSL3 q)) :=
  rationalExtend_unitaryRho k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc _

/-- Conjugation by a rational point of `T` multiplies the upper parameters by `χ z`, when
the embeddings of `χ z` are the values of the simple roots of `O` at the scalar extension
of `z`. -/
theorem conj_unitaryRho_upper (χ : rationalPoints T.toGrp → L)
    (hχ : ∀ z, ∀ a ∈ O, τ a (χ z) =
      (rootValue (p := p) (rationalPoints.map (CommGroupScheme.groupHom eT.inv)
        (rationalExtend k K T.toGrp z)) a : K))
    (z : rationalPoints T.toGrp) (q : SU3Root.Parameters c) :
    rationalPoints.map i z * URho (upperUnitary c q) * (rationalPoints.map i z)⁻¹ =
      URho (upperUnitary c (SU3Root.Parameters.scale (χ z) q)) := by
  apply rationalExtend_injective_of_isAffineHom k K
  rw [map_mul, map_mul, map_inv, rationalExtend_unitaryRho_upper,
    rationalExtend_unitaryRho_upper, rationalExtend_map, map_baseChange_map k K i p eT hT,
    PartnerData.conj_pairOrbitSL3]
  apply PartnerData.pairOrbitSL3_congr
  intro a ha
  exact diagConj_map_upperSL3 (τ a).toRingHom q (χ z) _ _ (hχ z a ha).symm
    ((hχ z _ (D.mem a ha)).symm.trans (hτc a ha (χ z)))

/-- Conjugation by a rational point of `T` multiplies the lower parameters by `χ z`, when
the embeddings of `χ z` are the inverse values of the partners of the simple roots of `O`. -/
theorem conj_unitaryRho_lower (χ : rationalPoints T.toGrp → L)
    (hχ : ∀ z, ∀ a ∈ O, τ a (χ z) =
      (((rootValue (p := p) (rationalPoints.map (CommGroupScheme.groupHom eT.inv)
        (rationalExtend k K T.toGrp z)) (D.partner a))⁻¹ : Kˣ) : K))
    (z : rationalPoints T.toGrp) (q : SU3Root.Parameters c) :
    rationalPoints.map i z * URho (lowerUnitary c q) * (rationalPoints.map i z)⁻¹ =
      URho (lowerUnitary c (SU3Root.Parameters.scale (χ z) q)) := by
  apply rationalExtend_injective_of_isAffineHom k K
  rw [map_mul, map_mul, map_inv, rationalExtend_unitaryRho_lower,
    rationalExtend_unitaryRho_lower, rationalExtend_map, map_baseChange_map k K i p eT hT,
    PartnerData.conj_pairOrbitSL3]
  apply PartnerData.pairOrbitSL3_congr
  intro a ha
  refine diagConj_map_lowerSL3 (τ a).toRingHom q (χ z) _ _ ?_ (hχ z a ha).symm
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hτc a ha, hχ z _ (D.mem a ha),
    D.partner_partner a ha]

variable [Smooth G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))} (iS : S.toGrp ⟶ G)
  (bS : characterLattice S) (hS : IsSplitTorus S.toGrp)

set_option hygiene false in
local notation "UK[" b "]" => Langlands.Geometry.Building.rootGroupPoints
  (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
  ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
  (characterLattice.baseChange (algebraBaseMap k K) S b)

section Upper

variable (hb0 : bS ≠ 0)
  (hmem : ∀ h : p.base.support → SL3 K, (∀ a ∈ O, IsUpperSL3 (h a)) →
    D.pairOrbitSL3 hAdj x h ∈ UK[bS])
  (hprod : ∀ g ∈ UK[bS], ∃ h : p.base.support → SL3 K, (∀ a ∈ O, IsUpperSL3 (h a)) ∧
    D.IsPairFamily h ∧ D.pairOrbitSL3 hAdj x h = g)
  (huniq : ∀ h h' : p.base.support → SL3 K, (∀ a ∈ O, IsUpperSL3 (h a)) →
    (∀ a ∈ O, IsUpperSL3 (h' a)) → D.IsPairFamily h → D.IsPairFamily h' →
    D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h' → ∀ a ∈ O, h a = h' a)
  (hfam : ∀ e : p.base.support → K,
    (∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → e (ρ σ a) = σ (e a)) →
      ∃ t : L, ∀ a ∈ O, e a = τ a t)
  {a₀ : p.base.support} (ha₀ : a₀ ∈ O)

include hS hb0 hmem in
theorem unitaryRho_upper_mem (q : SU3Root.Parameters c) :
    URho (upperUnitary c q) ∈ Langlands.Geometry.Building.rootGroupPoints iS bS := by
  rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS bS hb0,
    rationalExtend_unitaryRho_upper]
  exact hmem _ (fun a _ => (isUpperSL3_map_iff _ (τ a).toRingHom.injective _).mpr
    (isUpperSL3_upperSL3 q))

omit [Smooth G.X.hom] in
include huniq ha₀ in
theorem unitaryRho_upper_injective :
    Function.Injective fun q : SU3Root.Parameters c => URho (upperUnitary c q) := by
  intro q q' hqq
  have h1 := congrArg (rationalExtend k K G) hqq
  dsimp only at h1
  rw [rationalExtend_unitaryRho_upper, rationalExtend_unitaryRho_upper] at h1
  have h2 := huniq _ _
    (fun a _ => (isUpperSL3_map_iff _ (τ a).toRingHom.injective _).mpr (isUpperSL3_upperSL3 q))
    (fun a _ => (isUpperSL3_map_iff _ (τ a).toRingHom.injective _).mpr (isUpperSL3_upperSL3 q'))
    (isPairFamily_map k K p D τ c hτc (upperSL3_mem_twistFixedSubgroup q))
    (isPairFamily_map k K p D τ c hτc (upperSL3_mem_twistFixedSubgroup q')) h1 a₀ ha₀
  exact upperSL3_injective (specialLinearMap_injective _ (τ a₀).toRingHom.injective h2)

include hS hb0 hprod huniq hfam ha₀ in
theorem exists_unitaryRho_upper_eq {g : rationalPoints G}
    (hg : g ∈ Langlands.Geometry.Building.rootGroupPoints iS bS) :
    ∃ q : SU3Root.Parameters c, URho (upperUnitary c q) = g := by
  have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
    bS hb0 g).2 hg
  obtain ⟨h, hu, hh, hgh⟩ := hprod _ hgK
  obtain ⟨M, hM, hMh⟩ := exists_twistFixed_of_rationalExtend k K i hAdj p eT hT x hx hroot hρpair
    D hOs hπρ τ c hτc IsUpperSL3
    (fun σ g hg => (isUpperSL3_map_iff σ.toRingHom σ.toRingHom.injective g).mpr hg) huniq hfam
    ha₀ hu hh hgh.symm
  have hMu : IsUpperSL3 M := (isUpperSL3_map_iff _ (τ a₀).toRingHom.injective M).mp
    (by rw [hMh a₀ ha₀]; exact hu a₀ ha₀)
  obtain ⟨q, hq⟩ := exists_upperSL3_eq hMu hM
  refine ⟨q, rationalExtend_injective_of_isAffineHom k K ?_⟩
  rw [rationalExtend_unitaryRho_upper, hq, ← hgh]
  exact D.pairOrbitSL3_congr hAdj x hMh

/-- The upper root parameters as a homomorphism into the relative root group of `bS`. -/
def upperUnitaryHom :
    SU3Root.Parameters c →* Langlands.Geometry.Building.rootGroupPoints iS bS :=
  ((URho).comp (upperUnitary c)).codRestrict _
    (unitaryRho_upper_mem k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0
      hmem)

/-- Unitary root coordinates on the relative root group of `bS`. -/
def upperUnitaryEquiv :
    SU3Root.Parameters c ≃* Langlands.Geometry.Building.rootGroupPoints iS bS :=
  MulEquiv.ofBijective
    (upperUnitaryHom k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0 hmem)
    ⟨fun q q' h => unitaryRho_upper_injective k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ
        c hτc huniq ha₀ (congrArg Subtype.val h),
     fun y => by
      obtain ⟨q, hq⟩ := exists_unitaryRho_upper_eq k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
        τ hτ c hτc iS bS hS hb0 hprod huniq hfam ha₀ y.2
      exact ⟨q, Subtype.ext hq⟩⟩

theorem upperUnitaryEquiv_apply (q : SU3Root.Parameters c) :
    (upperUnitaryEquiv k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0 hmem
      hprod huniq hfam ha₀ q : rationalPoints G) = URho (upperUnitary c q) :=
  rfl

include hS huniq hfam ha₀ in
/-- The relative root group of `2 • bS` consists of the images of the central upper
parameters, given the analogous membership and product hypotheses. -/
theorem mem_double_iff_upper (h2b : 2 • bS ≠ 0)
    (hmem2 : ∀ h : p.base.support → SL3 K, (∀ a ∈ O, IsCentralUpperSL3 (h a)) →
      D.pairOrbitSL3 hAdj x h ∈ UK[2 • bS])
    (hprod2 : ∀ g ∈ UK[2 • bS], ∃ h : p.base.support → SL3 K,
      (∀ a ∈ O, IsCentralUpperSL3 (h a)) ∧ D.IsPairFamily h ∧ D.pairOrbitSL3 hAdj x h = g)
    (g : rationalPoints G) :
    g ∈ Langlands.Geometry.Building.rootGroupPoints iS (2 • bS) ↔
      ∃ q ∈ SU3Root.Parameters.central c, URho (upperUnitary c q) = g := by
  constructor
  · intro hg
    have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
      (2 • bS) h2b g).2 hg
    obtain ⟨h, hu, hh, hgh⟩ := hprod2 _ hgK
    obtain ⟨M, hM, hMh⟩ := exists_twistFixed_of_rationalExtend k K i hAdj p eT hT x hx hroot
      hρpair D hOs hπρ τ c hτc IsCentralUpperSL3
      (fun σ g hg => (isCentralUpperSL3_map_iff σ.toRingHom σ.toRingHom.injective g).mpr hg)
      (fun h h' h1 h2 => huniq h h' (fun a ha => (h1 a ha).1) (fun a ha => (h2 a ha).1)) hfam
      ha₀ hu hh hgh.symm
    have hMu : IsCentralUpperSL3 M :=
      (isCentralUpperSL3_map_iff _ (τ a₀).toRingHom.injective M).mp
        (by rw [hMh a₀ ha₀]; exact hu a₀ ha₀)
    obtain ⟨q, hq⟩ := exists_upperSL3_eq hMu.1 hM
    refine ⟨q, (isCentralUpperSL3_upperSL3_iff q).mp (hq ▸ hMu),
      rationalExtend_injective_of_isAffineHom k K ?_⟩
    rw [rationalExtend_unitaryRho_upper, hq, ← hgh]
    exact D.pairOrbitSL3_congr hAdj x hMh
  · rintro ⟨q, hq, rfl⟩
    rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
      (2 • bS) h2b, rationalExtend_unitaryRho_upper]
    exact hmem2 _ (fun a _ => (isCentralUpperSL3_map_iff _ (τ a).toRingHom.injective _).mpr
      ((isCentralUpperSL3_upperSL3_iff q).mpr hq))

end Upper

section Lower

variable (hb0 : bS ≠ 0)
  (hmem : ∀ h : p.base.support → SL3 K, (∀ a ∈ O, IsLowerSL3 (h a)) →
    D.pairOrbitSL3 hAdj x h ∈ UK[-bS])
  (hprod : ∀ g ∈ UK[-bS], ∃ h : p.base.support → SL3 K, (∀ a ∈ O, IsLowerSL3 (h a)) ∧
    D.IsPairFamily h ∧ D.pairOrbitSL3 hAdj x h = g)
  (huniq : ∀ h h' : p.base.support → SL3 K, (∀ a ∈ O, IsLowerSL3 (h a)) →
    (∀ a ∈ O, IsLowerSL3 (h' a)) → D.IsPairFamily h → D.IsPairFamily h' →
    D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h' → ∀ a ∈ O, h a = h' a)
  (hfam : ∀ e : p.base.support → K,
    (∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → e (ρ σ a) = σ (e a)) →
      ∃ t : L, ∀ a ∈ O, e a = τ a t)
  {a₀ : p.base.support} (ha₀ : a₀ ∈ O)

include hS hb0 hmem in
theorem unitaryRho_lower_mem (q : SU3Root.Parameters c) :
    URho (lowerUnitary c q) ∈ Langlands.Geometry.Building.rootGroupPoints iS (-bS) := by
  rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS (-bS)
    (neg_ne_zero.mpr hb0), rationalExtend_unitaryRho_lower]
  exact hmem _ (fun a _ => (isLowerSL3_map_iff _ (τ a).toRingHom.injective _).mpr
    (isLowerSL3_lowerSL3 q))

omit [Smooth G.X.hom] in
include huniq ha₀ in
theorem unitaryRho_lower_injective :
    Function.Injective fun q : SU3Root.Parameters c => URho (lowerUnitary c q) := by
  intro q q' hqq
  have h1 := congrArg (rationalExtend k K G) hqq
  dsimp only at h1
  rw [rationalExtend_unitaryRho_lower, rationalExtend_unitaryRho_lower] at h1
  have h2 := huniq _ _
    (fun a _ => (isLowerSL3_map_iff _ (τ a).toRingHom.injective _).mpr (isLowerSL3_lowerSL3 q))
    (fun a _ => (isLowerSL3_map_iff _ (τ a).toRingHom.injective _).mpr (isLowerSL3_lowerSL3 q'))
    (isPairFamily_map k K p D τ c hτc (lowerSL3_mem_twistFixedSubgroup q))
    (isPairFamily_map k K p D τ c hτc (lowerSL3_mem_twistFixedSubgroup q')) h1 a₀ ha₀
  exact lowerSL3_injective (specialLinearMap_injective _ (τ a₀).toRingHom.injective h2)

include hS hb0 hprod huniq hfam ha₀ in
theorem exists_unitaryRho_lower_eq {g : rationalPoints G}
    (hg : g ∈ Langlands.Geometry.Building.rootGroupPoints iS (-bS)) :
    ∃ q : SU3Root.Parameters c, URho (lowerUnitary c q) = g := by
  have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
    (-bS) (neg_ne_zero.mpr hb0) g).2 hg
  obtain ⟨h, hu, hh, hgh⟩ := hprod _ hgK
  obtain ⟨M, hM, hMh⟩ := exists_twistFixed_of_rationalExtend k K i hAdj p eT hT x hx hroot hρpair
    D hOs hπρ τ c hτc IsLowerSL3
    (fun σ g hg => (isLowerSL3_map_iff σ.toRingHom σ.toRingHom.injective g).mpr hg) huniq hfam
    ha₀ hu hh hgh.symm
  have hMu : IsLowerSL3 M := (isLowerSL3_map_iff _ (τ a₀).toRingHom.injective M).mp
    (by rw [hMh a₀ ha₀]; exact hu a₀ ha₀)
  obtain ⟨q, hq⟩ := exists_lowerSL3_eq hMu hM
  refine ⟨q, rationalExtend_injective_of_isAffineHom k K ?_⟩
  rw [rationalExtend_unitaryRho_lower, hq, ← hgh]
  exact D.pairOrbitSL3_congr hAdj x hMh

/-- The lower root parameters as a homomorphism into the relative root group of `-bS`. -/
def lowerUnitaryHom :
    SU3Root.Parameters c →* Langlands.Geometry.Building.rootGroupPoints iS (-bS) :=
  ((URho).comp (lowerUnitary c)).codRestrict _
    (unitaryRho_lower_mem k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0
      hmem)

/-- Unitary root coordinates on the relative root group of `-bS`. -/
def lowerUnitaryEquiv :
    SU3Root.Parameters c ≃* Langlands.Geometry.Building.rootGroupPoints iS (-bS) :=
  MulEquiv.ofBijective
    (lowerUnitaryHom k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0 hmem)
    ⟨fun q q' h => unitaryRho_lower_injective k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ
        c hτc huniq ha₀ (congrArg Subtype.val h),
     fun y => by
      obtain ⟨q, hq⟩ := exists_unitaryRho_lower_eq k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
        τ hτ c hτc iS bS hS hb0 hprod huniq hfam ha₀ y.2
      exact ⟨q, Subtype.ext hq⟩⟩

theorem lowerUnitaryEquiv_apply (q : SU3Root.Parameters c) :
    (lowerUnitaryEquiv k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc iS bS hS hb0 hmem
      hprod huniq hfam ha₀ q : rationalPoints G) = URho (lowerUnitary c q) :=
  rfl

include hS huniq hfam ha₀ in
/-- The relative root group of `2 • -bS` consists of the images of the central lower
parameters, given the analogous membership and product hypotheses. -/
theorem mem_double_iff_lower (h2b : 2 • -bS ≠ 0)
    (hmem2 : ∀ h : p.base.support → SL3 K, (∀ a ∈ O, IsCentralLowerSL3 (h a)) →
      D.pairOrbitSL3 hAdj x h ∈ UK[2 • -bS])
    (hprod2 : ∀ g ∈ UK[2 • -bS], ∃ h : p.base.support → SL3 K,
      (∀ a ∈ O, IsCentralLowerSL3 (h a)) ∧ D.IsPairFamily h ∧ D.pairOrbitSL3 hAdj x h = g)
    (g : rationalPoints G) :
    g ∈ Langlands.Geometry.Building.rootGroupPoints iS (2 • -bS) ↔
      ∃ q ∈ SU3Root.Parameters.central c, URho (lowerUnitary c q) = g := by
  constructor
  · intro hg
    have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
      (2 • -bS) h2b g).2 hg
    obtain ⟨h, hu, hh, hgh⟩ := hprod2 _ hgK
    obtain ⟨M, hM, hMh⟩ := exists_twistFixed_of_rationalExtend k K i hAdj p eT hT x hx hroot
      hρpair D hOs hπρ τ c hτc IsCentralLowerSL3
      (fun σ g hg => (isCentralLowerSL3_map_iff σ.toRingHom σ.toRingHom.injective g).mpr hg)
      (fun h h' h1 h2 => huniq h h' (fun a ha => (h1 a ha).1) (fun a ha => (h2 a ha).1)) hfam
      ha₀ hu hh hgh.symm
    have hMu : IsCentralLowerSL3 M :=
      (isCentralLowerSL3_map_iff _ (τ a₀).toRingHom.injective M).mp
        (by rw [hMh a₀ ha₀]; exact hu a₀ ha₀)
    obtain ⟨q, hq⟩ := exists_lowerSL3_eq hMu.1 hM
    refine ⟨q, (isCentralLowerSL3_lowerSL3_iff q).mp (hq ▸ hMu),
      rationalExtend_injective_of_isAffineHom k K ?_⟩
    rw [rationalExtend_unitaryRho_lower, hq, ← hgh]
    exact D.pairOrbitSL3_congr hAdj x hMh
  · rintro ⟨q, hq, rfl⟩
    rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
      (2 • -bS) h2b, rationalExtend_unitaryRho_lower]
    exact hmem2 _ (fun a _ => (isCentralLowerSL3_map_iff _ (τ a).toRingHom.injective _).mpr
      ((isCentralLowerSL3_lowerSL3_iff q).mpr hq))

end Lower

end Field

end Galois

end SplitPinning

end Langlands.GroupScheme
