import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Group.GL.BlockModulus

/-!
# All-field port of `Langlands.Group.GL.BlockModulus`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockModulus` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped BigOperators
open scoped NNReal
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u

variable {F : LocalFieldPackage.{u}}
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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable (F : LocalFieldPackage.{u})
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

end Langlands.AllFieldBZ.LocalFieldPackage
