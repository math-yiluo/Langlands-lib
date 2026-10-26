import Langlands.Representation.Exponents.DualJacquet

/-!
# Dual-detected character quotients and central defect images

The quotient and every image retain the full ambient group action.
The constructions require no finite nilpotence or nonvanishing hypothesis.
-/

noncomputable section

namespace Langlands

universe uR uG uH uV uF

namespace DualCharacterQuotient

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {H : Type uH} [CommGroup H] {V : Type uV} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V) (ι : H →* G)
  (hι : ∀ a, ι a ∈ Subgroup.center G) (χ : H →* Rˣ)

/-- The actual generalized character space in the transpose dual. -/
def dualSpace : Subrepresentation (commutativeTranspose (ρ.comp ι)) :=
  generalizedCommutativeCharacterSpace (commutativeTranspose (ρ.comp ι)) χ

/-- Precomposition by the full group action commutes with the central
transpose action. -/
def dualTranslate (g : G) :
    (commutativeTranspose (ρ.comp ι)).IntertwiningMap
      (commutativeTranspose (ρ.comp ι)) where
  toLinearMap := LinearMap.dualMap (ρ g)
  isIntertwining' a := by
    ext φ v
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply,
      commutativeTranspose_apply, MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.mp (hι a) g)]

include hι in
theorem dualTranslate_mem (g : G) {φ : Module.Dual R V}
    (hφ : φ ∈ dualSpace ρ ι χ) :
    φ.comp (ρ g) ∈ dualSpace ρ ι χ :=
  map_mem_generalizedCentralCharacterSpace (dualTranslate ρ ι hι g)
    (commutativeCentralCharacter χ) hφ

/-- The annihilator of the generalized dual space, invariant under all of `G`. -/
def annihilator : Subrepresentation ρ where
  toSubmodule := (dualSpace ρ ι χ).toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g := by
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    exact hv (φ.comp (ρ g)) (dualTranslate_mem ρ ι hι χ g hφ)

@[simp]
theorem mem_annihilator (v : V) :
    v ∈ annihilator ρ ι hι χ ↔
      ∀ φ : Module.Dual R V, φ ∈ dualSpace ρ ι χ → φ v = 0 :=
  Submodule.mem_dualCoannihilator v

/-- The actual quotient by the annihilator, in the original carrier universe. -/
def quotient : Rep.{uV} R G :=
  Rep.of (ρ.quotient (annihilator ρ ι hι χ).toSubmodule
    (annihilator ρ ι hι χ).apply_mem_toSubmodule)

/-- The actual full-group equivariant quotient map. -/
def quotientMap : ρ.IntertwiningMap (quotient ρ ι hι χ).ρ :=
  (Rep.mkQ (Rep.of ρ) (annihilator ρ ι hι χ).toSubmodule
    (annihilator ρ ι hι χ).apply_mem_toSubmodule).hom

theorem quotientMap_surjective : Function.Surjective (quotientMap ρ ι hι χ) :=
  (annihilator ρ ι hι χ).toSubmodule.mkQ_surjective

@[simp]
theorem quotientMap_eq_zero_iff (v : V) :
    quotientMap ρ ι hι χ v = 0 ↔
      ∀ φ : Module.Dual R V, φ ∈ dualSpace ρ ι χ → φ v = 0 := by
  change Submodule.Quotient.mk v = (0 : V ⧸ (annihilator ρ ι hι χ).toSubmodule) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_annihilator ρ ι hι χ v

/-- A detecting functional descends to the actual quotient. -/
def evaluation (φ : (dualSpace ρ ι χ).toSubmodule) :
    quotient ρ ι hι χ →ₗ[R] R :=
  (annihilator ρ ι hι χ).toSubmodule.liftQ φ.val (by
    intro v hv
    exact (mem_annihilator ρ ι hι χ v).mp hv φ.val φ.property)

@[simp]
theorem evaluation_quotientMap (φ : (dualSpace ρ ι χ).toSubmodule) (v : V) :
    evaluation ρ ι hι χ φ (quotientMap ρ ι hι χ v) = φ.val v := rfl

theorem eq_zero_iff (q : quotient ρ ι hι χ) :
    q = 0 ↔ ∀ φ : (dualSpace ρ ι χ).toSubmodule, evaluation ρ ι hι χ φ q = 0 := by
  obtain ⟨v, rfl⟩ := quotientMap_surjective ρ ι hι χ q
  rw [quotientMap_eq_zero_iff]
  constructor
  · intro h φ
    exact h φ.val φ.property
  · intro h φ hφ
    exact h ⟨φ, hφ⟩

/-- A central character defect is an endomorphism for the full group action. -/
def defect (a : H) :
    (quotient ρ ι hι χ).ρ.IntertwiningMap (quotient ρ ι hι χ).ρ where
  toLinearMap := (quotient ρ ι hι χ).ρ (ι a) - (χ a : R) • 1
  isIntertwining' g := by
    ext q
    change (quotient ρ ι hι χ).ρ (ι a) ((quotient ρ ι hι χ).ρ g q) -
        (χ a : R) • (quotient ρ ι hι χ).ρ g q =
      (quotient ρ ι hι χ).ρ g
        ((quotient ρ ι hι χ).ρ (ι a) q - (χ a : R) • q)
    rw [map_sub, map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply,
      ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hι a) g)]

@[simp]
theorem defect_toLinearMap (a : H) :
    (defect ρ ι hι χ a).toLinearMap =
      (quotient ρ ι hι χ).ρ (ι a) - (χ a : R) • 1 := rfl

@[simp]
theorem defect_apply (a : H) (q : quotient ρ ι hι χ) :
    defect ρ ι hι χ a q =
      (quotient ρ ι hι χ).ρ (ι a) q - (χ a : R) • q := rfl

theorem defect_pow_toLinearMap (a : H) (k : ℕ) :
    ((defect ρ ι hι χ a) ^ k).toLinearMap =
      ((quotient ρ ι hι χ).ρ (ι a) - (χ a : R) • 1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Representation.IntertwiningMap.coe_mul, ih, pow_succ]
      rfl

/-- Powers of the character defect commute with the quotient map. -/
theorem defect_pow_quotientMap (a : H) (k : ℕ) (v : V) :
    (defect ρ ι hι χ a ^ k) (quotientMap ρ ι hι χ v) =
      quotientMap ρ ι hι χ (((ρ (ι a) - (χ a : R) • 1) ^ k) v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Representation.IntertwiningMap.mul_apply, ih,
        defect_apply, pow_succ', Module.End.mul_apply]
      exact (map_sub (quotientMap ρ ι hι χ) _ _).symm

/-- Evaluation transports every defect power to its transpose on the dual. -/
theorem evaluation_defect_pow_quotientMap (a : H) (k : ℕ)
    (φ : (dualSpace ρ ι χ).toSubmodule) (v : V) :
    evaluation ρ ι hι χ φ ((defect ρ ι hι χ a ^ k) (quotientMap ρ ι hι χ v)) =
      (((commutativeTranspose (ρ.comp ι) a - (χ a : R) • 1) ^ k) φ.val) v := by
  rw [defect_pow_quotientMap, evaluation_quotientMap,
    commutativeTranspose_defect_pow_apply]
  rfl

theorem defect_pow_quotientMap_eq_zero_iff (a : H) (k : ℕ) (v : V) :
    (defect ρ ι hι χ a ^ k) (quotientMap ρ ι hι χ v) = 0 ↔
      ∀ φ : Module.Dual R V, φ ∈ dualSpace ρ ι χ →
        (((commutativeTranspose (ρ.comp ι) a - (χ a : R) • 1) ^ k) φ) v = 0 := by
  rw [defect_pow_quotientMap, quotientMap_eq_zero_iff]
  simp only [commutativeTranspose_defect_pow_apply]
  rfl

/-- The invariant range of the actual power of the central defect. -/
def defectRange (a : H) (k : ℕ) : Subrepresentation (quotient ρ ι hι χ).ρ :=
  (defect ρ ι hι χ a ^ k).range

@[simp]
theorem mem_defectRange (a : H) (k : ℕ) (q : quotient ρ ι hι χ) :
    q ∈ defectRange ρ ι hι χ a k ↔
      ∃ v : quotient ρ ι hι χ, (defect ρ ι hι χ a ^ k) v = q := Iff.rfl

/-- The range with its induced full-group representation. -/
def defectRangeRepresentation (a : H) (k : ℕ) : Rep.{uV} R G :=
  Rep.of (defectRange ρ ι hι χ a k).toRepresentation

/-- The defect power corestricted to its actual range. -/
def defectRangeProjection (a : H) (k : ℕ) :
    (quotient ρ ι hι χ).ρ.IntertwiningMap
      (defectRangeRepresentation ρ ι hι χ a k).ρ where
  toLinearMap := (defect ρ ι hι χ a ^ k).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact LinearMap.congr_fun ((defect ρ ι hι χ a ^ k).isIntertwining' g) q

theorem defectRangeProjection_surjective (a : H) (k : ℕ) :
    Function.Surjective (defectRangeProjection ρ ι hι χ a k) := by
  rintro ⟨q, v, hv⟩
  exact ⟨v, Subtype.ext hv⟩

/-- The actual inclusion of the defect image into the character quotient. -/
def defectRangeInclusion (a : H) (k : ℕ) :
    (defectRangeRepresentation ρ ι hι χ a k).ρ.IntertwiningMap
      (quotient ρ ι hι χ).ρ where
  toLinearMap := (defectRange ρ ι hι χ a k).toSubmodule.subtype
  isIntertwining' _ := rfl

/-- The surjective full-group intertwiner from the original representation. -/
def defectRangeMap (a : H) (k : ℕ) :
    ρ.IntertwiningMap (defectRangeRepresentation ρ ι hι χ a k).ρ :=
  (defectRangeProjection ρ ι hι χ a k).comp (quotientMap ρ ι hι χ)

theorem defectRangeMap_surjective (a : H) (k : ℕ) :
    Function.Surjective (defectRangeMap ρ ι hι χ a k) :=
  (defectRangeProjection_surjective ρ ι hι χ a k).comp
    (quotientMap_surjective ρ ι hι χ)

@[simp]
theorem defectRangeInclusion_projection (a : H) (k : ℕ)
    (q : quotient ρ ι hι χ) :
    defectRangeInclusion ρ ι hι χ a k (defectRangeProjection ρ ι hι χ a k q) =
      (defect ρ ι hι χ a ^ k) q := rfl

@[simp]
theorem defectRangeInclusion_map (a : H) (k : ℕ) (v : V) :
    defectRangeInclusion ρ ι hι χ a k (defectRangeMap ρ ι hι χ a k v) =
      (defect ρ ι hι χ a ^ k) (quotientMap ρ ι hι χ v) := rfl

theorem defectRangeInclusion_comp_map (a : H) (k : ℕ) :
    (defectRangeInclusion ρ ι hι χ a k).comp (defectRangeMap ρ ι hι χ a k) =
      (defect ρ ι hι χ a ^ k).comp (quotientMap ρ ι hι χ) := rfl

theorem defectRange_zero (a : H) : defectRange ρ ι hι χ a 0 = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  ext q
  exact ⟨fun _ => trivial, fun _ => ⟨q, rfl⟩⟩

end DualCharacterQuotient

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)
  (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
  (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)

/-- The annihilator of the actual generalized dual character space, invariant
under the full product Levi. -/
def dualJacquetCharacterAnnihilator :
    Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ :=
  DualCharacterQuotient.annihilator
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
    (B.blockScalarLevi F.Carrier) (B.blockScalarLevi_mem_center F.Carrier) χ

@[simp]
theorem mem_dualJacquetCharacterAnnihilator
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    v ∈ T.dualJacquetCharacterAnnihilator B A χ ↔
      ∀ φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A),
        φ ∈ generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ →
          φ v = 0 :=
  DualCharacterQuotient.mem_annihilator _ _ _ _ v

/-- The actual character-detected quotient of the full opposite Jacquet module. -/
def dualJacquetCharacterQuotient : Rep.{uV} ℂ (B.Levi F.Carrier) :=
  DualCharacterQuotient.quotient
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
    (B.blockScalarLevi F.Carrier) (B.blockScalarLevi_mem_center F.Carrier) χ

/-- The canonical full-Levi equivariant projection onto the character quotient. -/
def dualJacquetCharacterQuotientMap :
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.IntertwiningMap
      (T.dualJacquetCharacterQuotient B A χ).ρ :=
  DualCharacterQuotient.quotientMap _ _ _ _

theorem dualJacquetCharacterQuotientMap_surjective :
    Function.Surjective (T.dualJacquetCharacterQuotientMap B A χ) :=
  DualCharacterQuotient.quotientMap_surjective _ _ _ _

@[simp]
theorem dualJacquetCharacterQuotientMap_eq_zero_iff
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    T.dualJacquetCharacterQuotientMap B A χ v = 0 ↔
      ∀ φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A),
        φ ∈ generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ →
          φ v = 0 :=
  DualCharacterQuotient.quotientMap_eq_zero_iff _ _ _ _ v

/-- Evaluation of an actual generalized dual character functional on the quotient. -/
def dualJacquetCharacterEvaluation
    (φ : (generalizedCommutativeCharacterSpace
      (T.splitCentreDualJacquet B A).ρ χ).toSubmodule) :
    T.dualJacquetCharacterQuotient B A χ →ₗ[ℂ] ℂ :=
  DualCharacterQuotient.evaluation _ _ _ _ φ

@[simp]
theorem dualJacquetCharacterEvaluation_quotientMap
    (φ : (generalizedCommutativeCharacterSpace
      (T.splitCentreDualJacquet B A).ρ χ).toSubmodule)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    T.dualJacquetCharacterEvaluation B A χ φ
      (T.dualJacquetCharacterQuotientMap B A χ v) =
        (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from φ.val) v := rfl

theorem dualJacquetCharacterQuotient_eq_zero_iff
    (q : T.dualJacquetCharacterQuotient B A χ) :
    q = 0 ↔ ∀ φ : (generalizedCommutativeCharacterSpace
      (T.splitCentreDualJacquet B A).ρ χ).toSubmodule,
        T.dualJacquetCharacterEvaluation B A χ φ q = 0 :=
  DualCharacterQuotient.eq_zero_iff _ _ _ _ q

/-- The full-Levi endomorphism given by the block-scalar character defect. -/
def dualJacquetCharacterDefect (a : Fin B.length → F.Carrierˣ) :
    (T.dualJacquetCharacterQuotient B A χ).ρ.IntertwiningMap
      (T.dualJacquetCharacterQuotient B A χ).ρ :=
  DualCharacterQuotient.defect _ _ _ _ a

@[simp]
theorem dualJacquetCharacterDefect_toLinearMap (a : Fin B.length → F.Carrierˣ) :
    (T.dualJacquetCharacterDefect B A χ a).toLinearMap =
      (T.dualJacquetCharacterQuotient B A χ).ρ (B.blockScalarLevi F.Carrier a) -
        (χ a : ℂ) • 1 := rfl

@[simp]
theorem dualJacquetCharacterDefect_apply (a : Fin B.length → F.Carrierˣ)
    (q : T.dualJacquetCharacterQuotient B A χ) :
    T.dualJacquetCharacterDefect B A χ a q =
      (T.dualJacquetCharacterQuotient B A χ).ρ (B.blockScalarLevi F.Carrier a) q -
        (χ a : ℂ) • q := rfl

theorem dualJacquetCharacterDefect_pow_toLinearMap
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (T.dualJacquetCharacterDefect B A χ a ^ k).toLinearMap =
      ((T.dualJacquetCharacterQuotient B A χ).ρ (B.blockScalarLevi F.Carrier a) -
        (χ a : ℂ) • 1) ^ k :=
  DualCharacterQuotient.defect_pow_toLinearMap _ _ _ _ a k

theorem dualJacquetCharacterDefect_pow_quotientMap
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    (T.dualJacquetCharacterDefect B A χ a ^ k)
        (T.dualJacquetCharacterQuotientMap B A χ v) =
      T.dualJacquetCharacterQuotientMap B A χ
        ((((T.splitCentreOppositeJacquet B A).ρ a - (χ a : ℂ) • 1) ^ k) v) :=
  DualCharacterQuotient.defect_pow_quotientMap _ _ _ _ a k v

theorem dualJacquetCharacterEvaluation_defect_pow_quotientMap
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (φ : (generalizedCommutativeCharacterSpace
      (T.splitCentreDualJacquet B A).ρ χ).toSubmodule)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    T.dualJacquetCharacterEvaluation B A χ φ
        ((T.dualJacquetCharacterDefect B A χ a ^ k)
          (T.dualJacquetCharacterQuotientMap B A χ v)) =
      (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from
        (((T.splitCentreDualJacquet B A).ρ a - (χ a : ℂ) • 1) ^ k) φ.val) v :=
  DualCharacterQuotient.evaluation_defect_pow_quotientMap _ _ _ _ a k φ v

theorem dualJacquetCharacterDefect_pow_quotientMap_eq_zero_iff
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    (T.dualJacquetCharacterDefect B A χ a ^ k)
        (T.dualJacquetCharacterQuotientMap B A χ v) = 0 ↔
      ∀ φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A),
        φ ∈ generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ →
          (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from
            (((T.splitCentreDualJacquet B A).ρ a - (χ a : ℂ) • 1) ^ k) φ) v = 0 :=
  DualCharacterQuotient.defect_pow_quotientMap_eq_zero_iff _ _ _ _ a k v

/-- The actual full-Levi invariant image of a power of the central defect. -/
def dualJacquetCharacterDefectRange (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    Subrepresentation (T.dualJacquetCharacterQuotient B A χ).ρ :=
  DualCharacterQuotient.defectRange _ _ _ _ a k

@[simp]
theorem mem_dualJacquetCharacterDefectRange (a : Fin B.length → F.Carrierˣ)
    (k : ℕ) (q : T.dualJacquetCharacterQuotient B A χ) :
    q ∈ T.dualJacquetCharacterDefectRange B A χ a k ↔
      ∃ v : T.dualJacquetCharacterQuotient B A χ,
        (T.dualJacquetCharacterDefect B A χ a ^ k) v = q := Iff.rfl

/-- The actual defect image with its induced full-Levi representation. -/
def dualJacquetCharacterDefectRangeRepresentation
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) : Rep.{uV} ℂ (B.Levi F.Carrier) :=
  DualCharacterQuotient.defectRangeRepresentation
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
    (B.blockScalarLevi F.Carrier) (B.blockScalarLevi_mem_center F.Carrier) χ a k

/-- The defect power corestricted to its actual full-Levi image. -/
def dualJacquetCharacterDefectRangeProjection
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (T.dualJacquetCharacterQuotient B A χ).ρ.IntertwiningMap
      (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ :=
  DualCharacterQuotient.defectRangeProjection _ _ _ _ a k

theorem dualJacquetCharacterDefectRangeProjection_surjective
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    Function.Surjective (T.dualJacquetCharacterDefectRangeProjection B A χ a k) :=
  DualCharacterQuotient.defectRangeProjection_surjective _ _ _ _ a k

/-- The actual full-Levi inclusion of the central defect image. -/
def dualJacquetCharacterDefectRangeInclusion
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ.IntertwiningMap
      (T.dualJacquetCharacterQuotient B A χ).ρ :=
  DualCharacterQuotient.defectRangeInclusion _ _ _ _ a k

/-- The canonical surjection from the whole opposite Jacquet module to the image. -/
def dualJacquetCharacterDefectRangeMap (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.IntertwiningMap
      (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ :=
  DualCharacterQuotient.defectRangeMap _ _ _ _ a k

theorem dualJacquetCharacterDefectRangeMap_surjective
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    Function.Surjective (T.dualJacquetCharacterDefectRangeMap B A χ a k) :=
  DualCharacterQuotient.defectRangeMap_surjective _ _ _ _ a k

@[simp]
theorem dualJacquetCharacterDefectRangeProjection_apply
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (q : T.dualJacquetCharacterQuotient B A χ) :
    (T.dualJacquetCharacterDefectRangeProjection B A χ a k q).val =
      (T.dualJacquetCharacterDefect B A χ a ^ k) q := rfl

@[simp]
theorem dualJacquetCharacterDefectRangeMap_apply
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    (T.dualJacquetCharacterDefectRangeMap B A χ a k v).val =
      (T.dualJacquetCharacterDefect B A χ a ^ k)
        (T.dualJacquetCharacterQuotientMap B A χ v) := rfl

@[simp]
theorem dualJacquetCharacterDefectRangeInclusion_apply
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (w : T.dualJacquetCharacterDefectRangeRepresentation B A χ a k) :
    T.dualJacquetCharacterDefectRangeInclusion B A χ a k w = w.val := rfl

theorem dualJacquetCharacterDefectRangeInclusion_comp_projection
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (T.dualJacquetCharacterDefectRangeInclusion B A χ a k).comp
        (T.dualJacquetCharacterDefectRangeProjection B A χ a k) =
      T.dualJacquetCharacterDefect B A χ a ^ k := rfl

theorem dualJacquetCharacterDefectRangeInclusion_comp_map
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    (T.dualJacquetCharacterDefectRangeInclusion B A χ a k).comp
        (T.dualJacquetCharacterDefectRangeMap B A χ a k) =
      (T.dualJacquetCharacterDefect B A χ a ^ k).comp
        (T.dualJacquetCharacterQuotientMap B A χ) := rfl

theorem dualJacquetCharacterDefectRange_zero
    (a : Fin B.length → F.Carrierˣ) :
    T.dualJacquetCharacterDefectRange B A χ a 0 = ⊤ :=
  DualCharacterQuotient.defectRange_zero _ _ _ _ a

end PadicField.TopologicalData

end Langlands
