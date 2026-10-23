import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Exponents.NilpotenceIndex

/-!
# Split-center dual exponents and their uniform nilpotence orders

The full algebraic dual carries the transpose of the normalized opposite
Jacquet action on the commutative scalar torus. No inversion remains.
-/

noncomputable section

namespace Langlands

universe uR uA uV uF uG

section Commutative

variable {R : Type uR} [CommRing R] {A : Type uA} [CommGroup A]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Transposition gives a representation when the acting group is commutative. -/
def commutativeTranspose (ρ : Representation R A V) :
    Representation R A (Module.Dual R V) :=
  ρ.dual.comp (MonoidHom.id A)⁻¹

@[simp]
theorem commutativeTranspose_apply (ρ : Representation R A V) (a : A)
    (φ : Module.Dual R V) (v : V) :
    commutativeTranspose ρ a φ v = φ (ρ a v) := by
  simp [commutativeTranspose, Representation.dual]

/-- Powers of a character defect transpose without changing their order. -/
theorem commutativeTranspose_defect_pow_apply (ρ : Representation R A V)
    (a : A) (c : R) (k : ℕ) (φ : Module.Dual R V) (v : V) :
    (((commutativeTranspose ρ a - c • 1) ^ k) φ) v =
      φ (((ρ a - c • 1) ^ k) v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        commutativeTranspose_apply, ih]
      rw [pow_succ, Module.End.mul_apply]
      simp [map_sub, map_smul]

/-- Restrict a character to the full center of an abelian group. -/
def commutativeCentralCharacter (χ : A →* Rˣ) : Subgroup.center A →* Rˣ :=
  χ.comp (Subgroup.center A).subtype

/-- Uniform finite character spaces for an abelian action, reusing the actual
central subrepresentations. -/
def commutativeCharacterSpace (ρ : Representation R A V) (χ : A →* Rˣ)
    (k : ℕ) : Subrepresentation ρ :=
  centralCharacterSpace ρ (commutativeCentralCharacter χ) k

@[simp]
theorem mem_commutativeCharacterSpace (ρ : Representation R A V) (χ : A →* Rˣ)
    (k : ℕ) (v : V) :
    v ∈ commutativeCharacterSpace ρ χ k ↔
      ∀ a : A, ((ρ a - (χ a : R) • 1) ^ k) v = 0 := by
  rw [commutativeCharacterSpace, mem_centralCharacterSpace]
  constructor
  · intro h a
    exact h ⟨a, Subgroup.mem_center_iff.mpr (fun b => mul_comm b a)⟩
  · intro h a
    exact h (a : A)

@[simp]
theorem mem_commutativeCharacterSpace_one (ρ : Representation R A V)
    (χ : A →* Rˣ) (v : V) :
    v ∈ commutativeCharacterSpace ρ χ 1 ↔ ∀ a : A, ρ a v = (χ a : R) • v := by
  rw [mem_commutativeCharacterSpace]
  simp [sub_eq_zero]

/-- The actual increasing union of the uniform finite spaces. -/
def generalizedCommutativeCharacterSpace (ρ : Representation R A V) (χ : A →* Rˣ) :
    Subrepresentation ρ :=
  generalizedCentralCharacterSpace ρ (commutativeCentralCharacter χ)

@[simp]
theorem mem_generalizedCommutativeCharacterSpace (ρ : Representation R A V)
    (χ : A →* Rˣ) (v : V) :
    v ∈ generalizedCommutativeCharacterSpace ρ χ ↔
      ∃ k : ℕ, ∀ a : A, ((ρ a - (χ a : R) • 1) ^ k) v = 0 := by
  rw [generalizedCommutativeCharacterSpace, mem_generalizedCentralCharacterSpace]
  apply exists_congr
  intro k
  constructor
  · intro h a
    exact h ⟨a, Subgroup.mem_center_iff.mpr (fun b => mul_comm b a)⟩
  · intro h a
    exact h (a : A)

/-- The least uniform order of the entire generalized component, allowing infinity. -/
def commutativeCharacterNilpotenceIndex (ρ : Representation R A V) (χ : A →* Rˣ) : ℕ∞ :=
  centralCharacterNilpotenceIndex ρ (commutativeCentralCharacter χ)

theorem commutativeCharacterNilpotenceIndex_le_iff (ρ : Representation R A V)
    (χ : A →* Rˣ) (k : ℕ) :
    commutativeCharacterNilpotenceIndex ρ χ ≤ (k : ℕ∞) ↔
      generalizedCommutativeCharacterSpace ρ χ ≤ commutativeCharacterSpace ρ χ k :=
  centralCharacterNilpotenceIndex_le_iff ρ (commutativeCentralCharacter χ) k

end Commutative

namespace Jacquet

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- The actual full-dual functionals invariant under the subgroup. -/
def subgroupInvariantDual (ρ : Representation R G V) (N : Subgroup G) :
    Submodule R (Module.Dual R V) where
  carrier := {f | ∀ n : N, ∀ v : V, f (ρ n v) = f v}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg n v
    simp only [LinearMap.add_apply, hf n v, hg n v]
  smul_mem' := by
    intro r f hf n v
    simp only [LinearMap.smul_apply, hf n v]

/-- The quotient universal property identifies its full dual with the
subgroup-invariant functionals on the original representation. -/
def coinvariantsDualEquiv (ρ : Representation R G V) (N : Subgroup G) :
    Module.Dual R (Coinvariants ρ N) ≃ₗ[R] subgroupInvariantDual ρ N where
  toFun f := ⟨f.comp (mk ρ N), by
    intro n v
    change f (mk ρ N (ρ n v)) = f (mk ρ N v)
    rw [mk_apply_subgroup]⟩
  invFun f := lift ρ N f.val (by
    intro n
    ext v
    exact f.property n v)
  left_inv f := by
    apply Representation.Coinvariants.hom_ext
    rfl
  right_inv f := by
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coinvariantsDualEquiv_apply (ρ : Representation R G V) (N : Subgroup G)
    (f : Module.Dual R (Coinvariants ρ N)) (v : V) :
    (coinvariantsDualEquiv ρ N f).val v = f (mk ρ N v) := rfl

end Jacquet

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The actual normalized opposite Jacquet module restricted to block scalars. -/
def splitCentreOppositeJacquet (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Rep.{uV} ℂ (Fin B.length → F.Carrierˣ) :=
  Rep.of ((CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.comp
    (B.blockScalarLevi F.Carrier))

/-- Transpose action on the full algebraic dual of the normalized opposite
Jacquet module, restricted to the split center. -/
def splitCentreDualJacquet (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Rep.{uV} ℂ (Fin B.length → F.Carrierˣ) :=
  Rep.of (commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ)

/-- The actual opposite coinvariant quotient map, with its normalized target. -/
def splitCentreOppositeJacquetMk (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    A →ₗ[ℂ] T.splitCentreOppositeJacquet B A :=
  Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier)

theorem splitCentreOppositeJacquetMk_surjective
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Function.Surjective (T.splitCentreOppositeJacquetMk B A) :=
  Jacquet.mk_surjective _ _

/-- The full dual is exactly the opposite-unipotent-invariant source dual. -/
def splitCentreDualJacquetSourceEquiv (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Module.Dual ℂ (T.splitCentreOppositeJacquet B A) ≃ₗ[ℂ]
      Jacquet.subgroupInvariantDual A.ρ (B.oppositeUnipotentSubgroup F.Carrier) :=
  Jacquet.coinvariantsDualEquiv _ _

@[simp]
theorem splitCentreDualJacquetSourceEquiv_apply
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) (v : A) :
    (T.splitCentreDualJacquetSourceEquiv B A φ).val v =
      φ (T.splitCentreOppositeJacquetMk B A v) := rfl

theorem splitCentreOppositeJacquet_mk
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (a : Fin B.length → F.Carrierˣ) (v : A) :
    (T.splitCentreOppositeJacquet B A).ρ a (T.splitCentreOppositeJacquetMk B A v) =
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) •
        T.splitCentreOppositeJacquetMk B A
          (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v) := by
  change Jacquet.normalizedActionOfModulus _ _ _ _ _ _
    (Jacquet.mk _ _ v) = _
  rw [Jacquet.normalizedActionOfModulus_mk]
  congr 1
  simp [leviHalfModulus_apply]

/-- Character-defect powers commute with the actual quotient map. -/
theorem splitCentreOppositeJacquet_defect_pow_mk
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (a : Fin B.length → F.Carrierˣ) (c : ℂ) (k : ℕ) (v : A) :
    (((T.splitCentreOppositeJacquet B A).ρ a - c • 1) ^ k)
      (T.splitCentreOppositeJacquetMk B A v) =
    T.splitCentreOppositeJacquetMk B A
      (((((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) •
        A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a))) - c • 1) ^ k) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        splitCentreOppositeJacquet_mk, map_sub, map_smul]

@[simp]
theorem splitCentreDualJacquet_apply (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (a : Fin B.length → F.Carrierˣ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A))
    (v : T.splitCentreOppositeJacquet B A) :
    (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from
      (T.splitCentreDualJacquet B A).ρ a φ) v =
      φ ((T.splitCentreOppositeJacquet B A).ρ a v) :=
  commutativeTranspose_apply _ a φ v

theorem splitCentreDualJacquet_apply_mk
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (a : Fin B.length → F.Carrierˣ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) (v : A) :
    (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from
      (T.splitCentreDualJacquet B A).ρ a φ) (T.splitCentreOppositeJacquetMk B A v) =
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) *
        φ (T.splitCentreOppositeJacquetMk B A
          (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v)) := by
  rw [splitCentreDualJacquet_apply, splitCentreOppositeJacquet_mk, map_smul]
  rfl

/-- Evaluation of every dual character-defect power on source vectors. -/
theorem splitCentreDualJacquet_defect_pow_apply_mk
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (a : Fin B.length → F.Carrierˣ) (c : ℂ) (k : ℕ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) (v : A) :
    (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from
      (((T.splitCentreDualJacquet B A).ρ a - c • 1) ^ k) φ)
        (T.splitCentreOppositeJacquetMk B A v) =
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) ^ k *
        φ (T.splitCentreOppositeJacquetMk B A
          (((A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) -
            ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ * c) • 1) ^ k) v)) := by
  change (((commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a - c • 1) ^ k)
    φ) (T.splitCentreOppositeJacquetMk B A v) = _
  rw [commutativeTranspose_defect_pow_apply, splitCentreOppositeJacquet_defect_pow_mk]
  have he : (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) •
      A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) - c • 1 =
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) •
        (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) -
          ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ * c) • 1) := by
    simp [smul_sub, smul_smul]
  rw [he, smul_pow, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]

/-- All finite spaces agree with the source's uniformly nilpotent
opposite-invariant functionals, including the same power `k`. -/
theorem mem_dualJacquet_characterSpace_iff
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (k : ℕ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) :
    φ ∈ commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ k ↔
      ∀ (a : Fin B.length → F.Carrierˣ) (v : A),
        (T.splitCentreDualJacquetSourceEquiv B A φ).val
          (((A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) -
            ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ *
              (χ a : ℂ)) • 1) ^ k) v) = 0 := by
  change φ ∈ commutativeCharacterSpace
    (commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ) χ k ↔ _
  rw [mem_commutativeCharacterSpace]
  have heval (a : Fin B.length → F.Carrierˣ) (v : A) :
      (((commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a -
        (χ a : ℂ) • 1) ^ k) φ) (T.splitCentreOppositeJacquetMk B A v) =
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) ^ k *
        (T.splitCentreDualJacquetSourceEquiv B A φ).val
          (((A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) -
            ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ *
              (χ a : ℂ)) • 1) ^ k) v) :=
    T.splitCentreDualJacquet_defect_pow_apply_mk B A a (χ a : ℂ) k φ v
  constructor
  · intro h a v
    have he := congrArg (fun f : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) =>
      f (T.splitCentreOppositeJacquetMk B A v)) (h a)
    rw [heval] at he
    simpa using he
  · intro h a
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := T.splitCentreOppositeJacquetMk_surjective B A q
    rw [heval, h a v, mul_zero]
    rfl

/-- The normalized eigen-equation is exactly the unnormalized source equation:
the latter has the opposite half-modulus on its right-hand side. -/
theorem mem_dualJacquet_eigenspace_iff
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) :
    φ ∈ commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1 ↔
      ∀ (a : Fin B.length → F.Carrierˣ) (v : A),
        φ (T.splitCentreOppositeJacquetMk B A
          (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v)) =
        (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ *
          (χ a : ℂ) * φ (T.splitCentreOppositeJacquetMk B A v) := by
  change φ ∈ commutativeCharacterSpace
    (commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ) χ 1 ↔ _
  rw [mem_commutativeCharacterSpace_one]
  constructor
  · intro h a v
    have he := congrArg
      (fun f : T.splitCentreDualJacquet B A =>
        (show Module.Dual ℂ (T.splitCentreOppositeJacquet B A) from f)
          (T.splitCentreOppositeJacquetMk B A v)) (h a)
    change _ = (χ a : ℂ) * φ (T.splitCentreOppositeJacquetMk B A v) at he
    rw [commutativeTranspose_apply, splitCentreOppositeJacquet_mk, map_smul,
      smul_eq_mul] at he
    calc
      _ = (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ *
            ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) *
              φ (T.splitCentreOppositeJacquetMk B A
                (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v))) := by
        simp
      _ = _ := by rw [he, mul_assoc]
  · intro h a
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := T.splitCentreOppositeJacquetMk_surjective B A q
    change _ = (χ a : ℂ) * φ (T.splitCentreOppositeJacquetMk B A v)
    rw [commutativeTranspose_apply, splitCentreOppositeJacquet_mk, map_smul, h a v]
    rw [smul_eq_mul]
    simp [← mul_assoc]

/-- A smooth split-center character occurring in the actual dual eigenspace. -/
def IsDualJacquetExponent (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) : Prop :=
  letI := T.topology
  IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
    commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1 ≠ ⊥

/-- The unitary part of the actual dual spectrum. Its identification with the
source's weak class exponents remains a representation-theoretic obligation. -/
def IsUnitaryDualJacquetExponent (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) : Prop :=
  T.IsDualJacquetExponent B A χ ∧ ∀ a, ‖(χ a : ℂ)‖ = 1

/-- Uniform nilpotence order of the whole generalized dual-exponent component.
This is not its vector-space dimension or Jordan–Hölder multiplicity. -/
def dualJacquetExponentNilpotenceIndex (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) : ℕ∞ :=
  commutativeCharacterNilpotenceIndex (T.splitCentreDualJacquet B A).ρ χ

theorem dualJacquetExponentNilpotenceIndex_le_iff
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (k : ℕ) :
    T.dualJacquetExponentNilpotenceIndex B A χ ≤ (k : ℕ∞) ↔
      generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ ≤
        commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ k :=
  commutativeCharacterNilpotenceIndex_le_iff _ _ _

end PadicField.TopologicalData

end Langlands
