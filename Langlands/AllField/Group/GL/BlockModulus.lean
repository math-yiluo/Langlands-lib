import Langlands.Group.GL.BlockModulus
import Langlands.AllField.Group.GL.NormalizedCharacter
import Langlands.AllField.Group.GL.PadicBlocks
/-!
# Explicit positive block modulus characters

For the standard upper block parabolic the factor contributed by blocks `i < j`
is `|det m_i| ^ n_j / |det m_j| ^ n_i`. The character is built from these actual
determinants. Its interpretation as Haar scaling is a separate theorem.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe u

variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The actual normalized determinant of one diagonal block. -/
def blockDeterminantNorm (i : Fin B.length) : B.Levi F →* ℝ≥0ˣ where
  toFun m := T.determinantNorm (B.size i) (m i)
  map_one' := map_one _
  map_mul' m m' := (T.determinantNorm (B.size i)).map_mul (m i) (m' i)

@[simp]
theorem blockDeterminantNorm_apply (i : Fin B.length) (m : B.Levi F) :
    T.blockDeterminantNorm B i m = T.determinantNorm (B.size i) (m i) := rfl

/-- The full positive standard upper-block modulus formula on the actual Levi. -/
def leviModulus : B.Levi F →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (T.blockDeterminantNorm B i) ^ B.size j /
      (T.blockDeterminantNorm B j) ^ B.size i

theorem leviModulus_apply (m : B.Levi F) :
    T.leviModulus B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        T.determinantNorm (B.size i) (m i) ^ B.size j /
          T.determinantNorm (B.size j) (m j) ^ B.size i := by
  simp [leviModulus]

/-- Simultaneous norm-one determinant conditions define an actual open subgroup. -/
def normOneLevi : Subgroup (B.Levi F) :=
  ⨅ i : Fin B.length, (T.blockDeterminantNorm B i).ker

@[simp]
theorem mem_normOneLevi (m : B.Levi F) :
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
    IsOpen (T.normOneLevi B : Set (B.Levi F)) := by
  let := T.topology
  have h : ∀ i : Fin B.length,
      IsOpen {m : B.Levi F | T.determinantNorm (B.size i) (m i) = 1} := by
    intro i
    change IsOpen (Set.preimage (fun m : B.Levi F => m i)
      ((T.determinantNorm (B.size i)).ker : Set (GeneralLinear (B.size i) F)))
    exact (T.isOpen_ker_determinantNorm (B.size i)).preimage (continuous_apply i)
  convert isOpen_iInter_of_finite h using 1
  ext m
  simp

theorem isOpen_ker_leviModulus :
    letI := T.topology
    IsOpen ((T.leviModulus B).ker : Set (B.Levi F)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Subgroup.isOpen_mono (T.normOneLevi_le_ker_leviModulus B) (T.isOpen_normOneLevi B)

/-- The positive complex half of the full modulus, used for induction. -/
def leviHalfModulus : B.Levi F →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))

@[simp]
theorem leviHalfModulus_apply (m : B.Levi F) :
    (T.leviHalfModulus B m : ℂ) =
      ((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ) := rfl

theorem leviHalfModulus_eq_one (m : B.Levi F) :
    T.leviHalfModulus B m = 1 ↔ T.leviModulus B m = 1 := by
  simpa only [Jacquet.inverseHalfCharacter, MonoidHom.inv_apply, inv_eq_one,
    leviHalfModulus] using Jacquet.inverseHalfCharacter_eq_one (T.leviModulus B) m

theorem isOpen_ker_leviHalfModulus :
    letI := T.topology
    IsOpen ((T.leviHalfModulus B).ker : Set (B.Levi F)) := by
  let := T.topology
  have h : (T.leviHalfModulus B).ker = (T.leviModulus B).ker := by
    ext m
    exact T.leviHalfModulus_eq_one B m
  rw [h]
  exact T.isOpen_ker_leviModulus B

/-- The positive half character on the parabolic, through its actual projection. -/
def parabolicHalfModulus : B.parabolic F →* ℂˣ :=
  (T.leviHalfModulus B).comp (B.leviProjection F)

@[simp]
theorem parabolicHalfModulus_apply (g : B.parabolic F) :
    T.parabolicHalfModulus B g =
      T.leviHalfModulus B (B.leviProjection F g) := rfl

@[simp]
theorem parabolicHalfModulus_section (m : B.Levi F) :
    T.parabolicHalfModulus B (B.leviInParabolic F m) =
      T.leviHalfModulus B m := by
  simp

theorem isOpen_ker_parabolicHalfModulus :
    letI := T.topology
    IsOpen ((T.parabolicHalfModulus B).ker : Set (B.parabolic F)) := by
  let := T.topology
  exact (T.isOpen_ker_leviHalfModulus B).preimage (T.blockLeviProjection B).continuous

end Langlands.LocalFieldData

namespace Langlands

universe u

variable (F : Type u) [Field F]
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

end Langlands
