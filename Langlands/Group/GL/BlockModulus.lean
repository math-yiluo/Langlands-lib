import Langlands.Group.GL.PadicBlocks
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Jacquet.PositiveCharacter

/-!
# Explicit positive block modulus characters

For the standard upper block parabolic the factor contributed by blocks `i < j`
is `|det m_i| ^ n_j / |det m_j| ^ n_i`. The character is built from these actual
determinants. Its interpretation as Haar scaling is a separate theorem.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The actual normalized determinant of one diagonal block. -/
def blockDeterminantNorm (i : Fin B.length) : B.Levi F.Carrier →* ℝ≥0ˣ where
  toFun m := T.determinantNorm (B.size i) (m i)
  map_one' := map_one _
  map_mul' m m' := (T.determinantNorm (B.size i)).map_mul (m i) (m' i)

@[simp]
theorem blockDeterminantNorm_apply (i : Fin B.length) (m : B.Levi F.Carrier) :
    T.blockDeterminantNorm B i m = T.determinantNorm (B.size i) (m i) := rfl

/-- The full positive standard upper-block modulus formula on the actual Levi. -/
def leviModulus : B.Levi F.Carrier →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (T.blockDeterminantNorm B i) ^ B.size j /
      (T.blockDeterminantNorm B j) ^ B.size i

theorem leviModulus_apply (m : B.Levi F.Carrier) :
    T.leviModulus B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        T.determinantNorm (B.size i) (m i) ^ B.size j /
          T.determinantNorm (B.size j) (m j) ^ B.size i := by
  simp [leviModulus]

/-- The same full positive character, inflated by the actual Levi projection. -/
def parabolicModulus : B.parabolic F.Carrier →* ℝ≥0ˣ :=
  (T.leviModulus B).comp (B.leviProjection F.Carrier)

@[simp]
theorem parabolicModulus_apply (g : B.parabolic F.Carrier) :
    T.parabolicModulus B g =
      T.leviModulus B (B.leviProjection F.Carrier g) := rfl

@[simp]
theorem parabolicModulus_section (m : B.Levi F.Carrier) :
    T.parabolicModulus B (B.leviInParabolic F.Carrier m) = T.leviModulus B m := by
  simp

/-- The modulus formula is trivial on the actual unipotent radical. -/
@[simp]
theorem parabolicModulus_unipotent (u : B.unipotentRadical F.Carrier) :
    T.parabolicModulus B u = 1 := by
  have hu : B.leviProjection F.Carrier u = 1 := u.property
  simp [hu]

/-- Simultaneous norm-one determinant conditions define an actual open subgroup. -/
def normOneLevi : Subgroup (B.Levi F.Carrier) :=
  ⨅ i : Fin B.length, (T.blockDeterminantNorm B i).ker

@[simp]
theorem mem_normOneLevi (m : B.Levi F.Carrier) :
    m ∈ T.normOneLevi B ↔
      ∀ i, T.determinantNorm (B.size i) (m i) = 1 := by
  simp [normOneLevi, MonoidHom.mem_ker]

theorem normOneLevi_le_ker_leviModulus :
    T.normOneLevi B ≤ (T.leviModulus B).ker := by
  intro m hm
  have h := (T.mem_normOneLevi B m).mp hm
  change T.leviModulus B m = 1
  simp [T.leviModulus_apply B, h]

theorem isOpen_normOneLevi :
    letI := T.topology
    IsOpen (T.normOneLevi B : Set (B.Levi F.Carrier)) := by
  let := T.topology
  have h : ∀ i : Fin B.length,
      IsOpen {m : B.Levi F.Carrier | T.determinantNorm (B.size i) (m i) = 1} := by
    intro i
    change IsOpen (Set.preimage (fun m : B.Levi F.Carrier => m i)
      ((T.determinantNorm (B.size i)).ker : Set (GeneralLinear (B.size i) F.Carrier)))
    exact (T.isOpen_ker_determinantNorm (B.size i)).preimage (continuous_apply i)
  convert isOpen_iInter_of_finite h using 1
  ext m
  simp

theorem isOpen_ker_leviModulus :
    letI := T.topology
    IsOpen ((T.leviModulus B).ker : Set (B.Levi F.Carrier)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Subgroup.isOpen_mono (T.normOneLevi_le_ker_leviModulus B) (T.isOpen_normOneLevi B)

theorem isOpen_ker_parabolicModulus :
    letI := T.topology
    IsOpen ((T.parabolicModulus B).ker : Set (B.parabolic F.Carrier)) := by
  let := T.topology
  exact (T.isOpen_ker_leviModulus B).preimage (T.blockLeviProjection B).continuous

/-- Continuity for the product of the actual block determinant norms. -/
theorem continuous_leviModulus :
    letI := T.topology
    Continuous (T.leviModulus B) := by
  let := T.topology
  change Continuous (fun m : B.Levi F.Carrier => T.leviModulus B m)
  simp_rw [T.leviModulus_apply B]
  simp only [div_eq_mul_inv]
  exact continuous_finsetProd _ fun i _ =>
    continuous_finsetProd _ fun j _ =>
      (((T.determinantNormContinuous (B.size i)).continuous.comp
        (continuous_apply i)).pow _).mul
      (((T.determinantNormContinuous (B.size j)).continuous.comp
        (continuous_apply j)).pow _).inv

/-- Continuity on the actual parabolic uses its proved continuous projection. -/
theorem continuous_parabolicModulus :
    letI := T.topology
    Continuous (T.parabolicModulus B) := by
  let := T.topology
  exact (T.continuous_leviModulus B).comp (T.blockLeviProjection B).continuous

/-- Every pair of block contributions cancels on an ambient scalar matrix. -/
@[simp]
theorem leviModulus_scalar (a : F.Carrierˣ) :
    T.leviModulus B (fun i => GeneralLinear.scalar (n := B.size i) a) = 1 := by
  rw [T.leviModulus_apply]
  simp only [T.determinantNorm_scalar]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm (B.size i) (B.size j)]
  exact div_self' _

/-- The positive complex half of the full modulus, used for induction. -/
def leviHalfModulus : B.Levi F.Carrier →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))

@[simp]
theorem leviHalfModulus_apply (m : B.Levi F.Carrier) :
    (T.leviHalfModulus B m : ℂ) =
      ((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ) := rfl

theorem leviHalfModulus_sq (m : B.Levi F.Carrier) :
    T.leviHalfModulus B m ^ 2 = Jacquet.complexCharacter (T.leviModulus B) m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, leviHalfModulus_apply, Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

theorem leviHalfModulus_eq_one (m : B.Levi F.Carrier) :
    T.leviHalfModulus B m = 1 ↔ T.leviModulus B m = 1 := by
  simpa only [Jacquet.inverseHalfCharacter, MonoidHom.inv_apply, inv_eq_one,
    leviHalfModulus] using Jacquet.inverseHalfCharacter_eq_one (T.leviModulus B) m

theorem isOpen_ker_leviHalfModulus :
    letI := T.topology
    IsOpen ((T.leviHalfModulus B).ker : Set (B.Levi F.Carrier)) := by
  let := T.topology
  have h : (T.leviHalfModulus B).ker = (T.leviModulus B).ker := by
    ext m
    exact T.leviHalfModulus_eq_one B m
  rw [h]
  exact T.isOpen_ker_leviModulus B

/-- The positive half character on the parabolic, through its actual projection. -/
def parabolicHalfModulus : B.parabolic F.Carrier →* ℂˣ :=
  (T.leviHalfModulus B).comp (B.leviProjection F.Carrier)

@[simp]
theorem parabolicHalfModulus_apply (g : B.parabolic F.Carrier) :
    T.parabolicHalfModulus B g =
      T.leviHalfModulus B (B.leviProjection F.Carrier g) := rfl

@[simp]
theorem parabolicHalfModulus_section (m : B.Levi F.Carrier) :
    T.parabolicHalfModulus B (B.leviInParabolic F.Carrier m) =
      T.leviHalfModulus B m := by
  simp

@[simp]
theorem parabolicHalfModulus_unipotent (u : B.unipotentRadical F.Carrier) :
    T.parabolicHalfModulus B u = 1 := by
  have hu : B.leviProjection F.Carrier u = 1 := u.property
  simp [hu]

theorem isOpen_ker_parabolicHalfModulus :
    letI := T.topology
    IsOpen ((T.parabolicHalfModulus B).ker : Set (B.parabolic F.Carrier)) := by
  let := T.topology
  exact (T.isOpen_ker_leviHalfModulus B).preimage (T.blockLeviProjection B).continuous

/-- The Jacquet convention is exactly the inverse of the induction half. -/
theorem inverseHalf_leviModulus :
    Jacquet.inverseHalfCharacter (T.leviModulus B) = (T.leviHalfModulus B)⁻¹ := rfl

/-- Changing compatible realizations changes neither determinant nor block modulus. -/
theorem leviModulus_eq (U : F.TopologicalData) :
    T.leviModulus B = U.leviModulus B := by
  ext m
  simp only [T.leviModulus_apply B, U.leviModulus_apply B, T.determinantNorm_eq U]

theorem parabolicModulus_eq (U : F.TopologicalData) :
    T.parabolicModulus B = U.parabolicModulus B := by
  simp only [parabolicModulus, T.leviModulus_eq B U]

theorem leviHalfModulus_eq (U : F.TopologicalData) :
    T.leviHalfModulus B = U.leviHalfModulus B := by
  simp only [leviHalfModulus, T.leviModulus_eq B U]

theorem parabolicHalfModulus_eq (U : F.TopologicalData) :
    T.parabolicHalfModulus B = U.parabolicHalfModulus B := by
  simp only [parabolicHalfModulus, T.leviHalfModulus_eq B U]

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The full positive block character for every algebraic p-adic field. -/
abbrev canonicalLeviModulus : B.Levi F.Carrier →* ℝ≥0ˣ :=
  F.canonicalTopologicalData.leviModulus B

/-- Its inflation to the actual standard parabolic. -/
abbrev canonicalParabolicModulus : B.parabolic F.Carrier →* ℝ≥0ˣ :=
  F.canonicalTopologicalData.parabolicModulus B

/-- The positive induction half for every algebraic p-adic field. -/
abbrev canonicalLeviHalfModulus : B.Levi F.Carrier →* ℂˣ :=
  F.canonicalTopologicalData.leviHalfModulus B

/-- The same positive half on the actual parabolic. -/
abbrev canonicalParabolicHalfModulus : B.parabolic F.Carrier →* ℂˣ :=
  F.canonicalTopologicalData.parabolicHalfModulus B

theorem isOpen_ker_canonicalLeviModulus :
    letI := F.canonicalLeviTopology B
    IsOpen ((F.canonicalLeviModulus B).ker : Set (B.Levi F.Carrier)) :=
  F.canonicalTopologicalData.isOpen_ker_leviModulus B

theorem isOpen_ker_canonicalParabolicModulus :
    letI := F.canonicalParabolicTopology B
    IsOpen ((F.canonicalParabolicModulus B).ker : Set (B.parabolic F.Carrier)) :=
  F.canonicalTopologicalData.isOpen_ker_parabolicModulus B

theorem isOpen_ker_canonicalLeviHalfModulus :
    letI := F.canonicalLeviTopology B
    IsOpen ((F.canonicalLeviHalfModulus B).ker : Set (B.Levi F.Carrier)) :=
  F.canonicalTopologicalData.isOpen_ker_leviHalfModulus B

theorem isOpen_ker_canonicalParabolicHalfModulus :
    letI := F.canonicalParabolicTopology B
    IsOpen ((F.canonicalParabolicHalfModulus B).ker : Set (B.parabolic F.Carrier)) :=
  F.canonicalTopologicalData.isOpen_ker_parabolicHalfModulus B

end Langlands.PadicField
