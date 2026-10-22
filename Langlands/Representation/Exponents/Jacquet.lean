import Langlands.Representation.Jacquet.Parabolic
import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Exponents of normalized Jacquet modules along the split centre

For a standard block parabolic of `GL_n(F)` the split centre of its Levi is the
group of block scalars `(a_1 1_{n_1}, …, a_r 1_{n_r})`. An exponent of `ρ` along
the parabolic is a smooth character of `(F^×)^r` that occurs as a generalized
eigencharacter of the normalized Jacquet module restricted to the split centre.
Its real part is the vector `x` with `|χ(a)| = ∏ |a_i|^(x_i)`.
-/

noncomputable section

namespace Langlands

universe uR uA uV uF

section Generic

variable {R : Type uR} [CommRing R] {A : Type uA} [Monoid A]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- Vectors killed by the `k`-th power of `π(a) - χ(a)` for every `a`. -/
def characterSpace (π : Representation R A V) (χ : A →* Rˣ) (k : ℕ) : Submodule R V :=
  ⨅ a : A, Module.End.genEigenspace (π a) (χ a : R) k

@[simp]
theorem mem_characterSpace (π : Representation R A V) (χ : A →* Rˣ) (k : ℕ) (v : V) :
    v ∈ characterSpace π χ k ↔ ∀ a : A, ((π a - (χ a : R) • 1) ^ k) v = 0 := by
  simp only [characterSpace, Submodule.mem_iInf, Module.End.mem_genEigenspace_nat,
    LinearMap.mem_ker]

/-- `χ` is a generalized eigencharacter of `π`: some nonzero vector is killed by a
single power of `π(a) - χ(a)` for every `a`. -/
def IsGeneralizedEigencharacter (π : Representation R A V) (χ : A →* Rˣ) : Prop :=
  ∃ k : ℕ, characterSpace π χ k ≠ ⊥

theorem isGeneralizedEigencharacter_iff (π : Representation R A V) (χ : A →* Rˣ) :
    IsGeneralizedEigencharacter π χ ↔
      ∃ (k : ℕ) (v : V), v ≠ 0 ∧ ∀ a : A, ((π a - (χ a : R) • 1) ^ k) v = 0 := by
  simp only [IsGeneralizedEigencharacter, Submodule.ne_bot_iff, mem_characterSpace]
  constructor
  · rintro ⟨k, v, hv, h⟩
    exact ⟨k, v, h, hv⟩
  · rintro ⟨k, v, h, hv⟩
    exact ⟨k, v, hv, h⟩

/-- An eigenvector for `χ` makes `χ` a generalized eigencharacter. -/
theorem isGeneralizedEigencharacter_of_eigenvector (π : Representation R A V)
    (χ : A →* Rˣ) {v : V} (hv : v ≠ 0) (h : ∀ a : A, π a v = (χ a : R) • v) :
    IsGeneralizedEigencharacter π χ := by
  refine (isGeneralizedEigencharacter_iff π χ).mpr ⟨1, v, hv, fun a => ?_⟩
  simp [h a]

end Generic

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (F : Type uF) [CommRing F]

/-- Block scalars are central in the block Levi. -/
theorem blockScalarLevi_mem_center (a : Fin B.length → Fˣ) :
    B.blockScalarLevi F a ∈ Subgroup.center (B.Levi F) := by
  rw [Subgroup.mem_center_iff]
  intro m
  funext i
  change m i * GeneralLinear.scalar (a i) = GeneralLinear.scalar (a i) * m i
  exact (Subgroup.mem_center_iff.mp (GeneralLinear.scalarToCenter (n := B.size i) (a i)).2
    (m i))

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Exponent

variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The normalized Jacquet module along `B`, restricted to the split centre of the
Levi. -/
def splitCentreJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (Fin B.length → F.Carrierˣ) (B.JacquetModule ρ) :=
  (T.normalizedJacquet B ρ).comp (B.blockScalarLevi F.Carrier)

theorem splitCentreJacquet_mk (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (a : Fin B.length → F.Carrierˣ) (v : V) :
    T.splitCentreJacquet B ρ a (B.jacquetMk ρ v) =
      (((NNReal.sqrt (T.leviModulus B (B.blockScalarLevi F.Carrier a) : NNReal) : ℝ) : ℂ))⁻¹ •
        B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v) :=
  T.normalizedJacquet_mk B ρ _ v

/-- `χ` is an exponent of `ρ` along the standard block parabolic of `B`: a smooth
character of `(F^×)^r` that is a generalized eigencharacter of the normalized
Jacquet module on the split centre. -/
def IsJacquetExponent (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) : Prop :=
  letI := T.topology
  IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
    IsGeneralizedEigencharacter (T.splitCentreJacquet B ρ) χ

end Exponent

/-- `x` is the real part of the character `χ` of `(F^×)^r`:
`|χ(a)| = ∏ |a_i|^(x_i)` for the residue-normalized absolute value. -/
def IsRealPartOf {r : ℕ} (χ : (Fin r → F.Carrierˣ) →* ℂˣ) (x : Fin r → ℝ) : Prop :=
  ∀ a : Fin r → F.Carrierˣ, ‖(χ a : ℂ)‖ = ∏ i, T.normalizedAbs (a i : F.Carrier) ^ x i

variable {T}

/-- The real part of a character is unique. -/
theorem IsRealPartOf.eq {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ} {x y : Fin r → ℝ}
    (hx : T.IsRealPartOf χ x) (hy : T.IsRealPartOf χ y) : x = y := by
  funext i
  have hϖ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  let u : F.Carrierˣ := Units.mk0 T.uniformizer hϖ
  have h := (hx (Pi.mulSingle i u : Fin r → F.Carrierˣ)).symm.trans
    (hy (Pi.mulSingle i u : Fin r → F.Carrierˣ))
  have hsingle : ∀ z : Fin r → ℝ,
      ∏ j, T.normalizedAbs (((Pi.mulSingle i u : Fin r → F.Carrierˣ) j : F.Carrierˣ) : F.Carrier) ^ z j =
        T.normalizedAbs T.uniformizer ^ z i := by
    intro z
    rw [Fintype.prod_eq_single i]
    · simp [u]
    · intro j hj
      rw [Pi.mulSingle_eq_of_ne hj, Units.val_one, T.normalizedAbs_one, Real.one_rpow]
  rw [hsingle x, hsingle y] at h
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hb : 0 < T.normalizedAbs T.uniformizer := T.normalizedAbs_pos hϖ
  have hlog : Real.log (T.normalizedAbs T.uniformizer) ≠ 0 := by
    rw [T.normalizedAbs_uniformizer, zpow_neg, zpow_one, Real.log_inv]
    exact neg_ne_zero.mpr (Real.log_pos hq).ne'
  have hl := congrArg Real.log h
  rw [Real.log_rpow hb, Real.log_rpow hb] at hl
  exact mul_right_cancel₀ hlog hl

end PadicField.TopologicalData

end Langlands
