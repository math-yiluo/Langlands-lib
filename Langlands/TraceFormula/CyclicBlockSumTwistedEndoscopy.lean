import Langlands.TraceFormula.CyclicRelativeWeilBlockSum
import Langlands.Global.HeckeCharacterTransport
import Mathlib.Data.Matrix.PEquiv

/-! # The twisted endoscopic condition for the cyclic block embedding -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.TraceFormula.CyclicBlockSum

open NumberField Langlands.ClassFieldTheory.Global Langlands.Global
open scoped NumberField

variable {I : Type v} [AddCommGroup I]

private theorem toAdd_one' : (1 : Multiplicative I).toAdd = (0 : I) := rfl

private theorem toAdd_mul' (x y : Multiplicative I) : (x * y).toAdd = x.toAdd + y.toAdd := rfl

section Matrices

variable [Fintype I] [DecidableEq I]

/-- Relabelling of the block index by translation by `ι`. -/
def blockShiftEquiv (b : ℕ) (ι : I) : Fin b × I ≃ Fin b × I :=
  (Equiv.refl (Fin b)).prodCongr (Equiv.addRight ι)

/-- The permutation matrix of the block relabelling `α ↦ α + ι`, as an invertible matrix. -/
def blockShift (b : ℕ) (ι : I) : BlockGL I b where
  val := (blockShiftEquiv b ι).toPEquiv.toMatrix
  inv := (blockShiftEquiv b ι).symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- Conjugating a block diagonal matrix by `blockShift b ι` moves the block at `α + ι`
to the position `α`. -/
theorem blockShift_conj_blockDiag (b : ℕ) (ι : I) (d : I → DualGL b) :
    blockShift b ι * blockDiag b d * (blockShift b ι)⁻¹ =
      blockDiag b (fun α => d (α + ι)) := by
  apply Units.ext
  change (blockShiftEquiv b ι).toPEquiv.toMatrix * Matrix.blockDiagonal (fun α => (d α).val) *
      (blockShiftEquiv b ι).symm.toPEquiv.toMatrix =
    Matrix.blockDiagonal (fun α => (d (α + ι)).val)
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
  ext ⟨j, α⟩ ⟨j', α'⟩
  simp only [Matrix.submatrix_apply, id, blockShiftEquiv, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.coe_addRight, Prod.map, Matrix.blockDiagonal_apply',
    add_left_inj]

omit [AddCommGroup I] in
/-- A block diagonal matrix with every block equal to the same scalar is that scalar. -/
theorem blockDiag_scalar (b : ℕ) (z : ℂˣ) :
    blockDiag (I := I) b (fun _ => Matrix.GeneralLinearGroup.scalar (Fin b) z) =
      Matrix.GeneralLinearGroup.scalar (Fin b × I) z := by
  apply Units.ext
  change Matrix.blockDiagonal (fun _ : I => Matrix.scalar (Fin b) (z : ℂ)) =
    Matrix.scalar (Fin b × I) (z : ℂ)
  ext ⟨j, α⟩ ⟨j', α'⟩
  by_cases h : α = α'
  · subst h
    simp [Matrix.blockDiagonal_apply_eq, Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ h]
    simp [Matrix.scalar_apply, h]

end Matrices

private theorem scalar_commute' (b : ℕ) (z : ℂˣ) (g : DualGL b) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin b) z) g := by
  apply Units.ext
  exact Matrix.scalar_comm (z : ℂ) (Commute.all _) g.val

section Relative

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

set_option hygiene false in
local notation "WR" => RelativeWeilGroup c F E

variable (κ : (E ≃ₐ[F] E) ≃* Multiplicative I)

set_option hygiene false in
local notation "k" => degree c F E κ

variable (r : I → WR) (hr : ∀ i, degree c F E κ (r i) = Multiplicative.ofAdd i)

set_option hygiene false in
local notation "dcl" => ideleDefect c F E κ r hr

/-- The Shapiro cocycle of a character `ω` of `C_E`: its value at `w` in the outer factor
`i` is `ω(δ_i(w))`. -/
def shapiroCocycle (ω : HeckeCharacter E) (w : WR) (i : I) : ℂˣ :=
  ω (dcl i w)

/-- The cocycle law for the shifted action of the relative Weil group. -/
theorem shapiroCocycle_mul (ω : HeckeCharacter E) (w w' : WR) (i : I) :
    shapiroCocycle c F E κ r hr ω (w * w') i =
      shapiroCocycle c F E κ r hr ω w i *
        shapiroCocycle c F E κ r hr ω w' (i + (k w).toAdd) := by
  simp only [shapiroCocycle, ideleDefect_mul, map_mul]

/-- On the idele classes of `E`, the cocycle reads `ω` at the conjugate by the transversal. -/
theorem shapiroCocycle_inclusion (ω : HeckeCharacter E) (a : IdeleClassGroup (𝓞 E) E) (i : I) :
    shapiroCocycle c F E κ r hr ω (RelativeWeilGroup.inclusion c F E a) i =
      ω (AdelicFunctoriality.ideleClassEquiv
        (RelativeWeilGroup.projection c F E (r i)).toRingEquiv a) := by
  simp only [shapiroCocycle, ideleDefect_inclusion]

variable (σ : E ≃ₐ[F] E)

include hr in
/-- The transversal at the label of `σ` projects to `σ`. -/
theorem projection_transversal :
    RelativeWeilGroup.projection c F E (r (κ σ).toAdd) = σ := by
  apply κ.injective
  have h := hr (κ σ).toAdd
  change κ (RelativeWeilGroup.projection c F E (r (κ σ).toAdd)) = _ at h
  rw [h]
  rfl

/-- The comparison of defects under conjugation by the transversal of `σ`:
`ε_i δ_(i+ι)(w) = σ(δ_i(w)) ε_(i+k(w))`, where `ι` is the label of `σ` and
`ε_i = δ_ι(r_i)`. -/
theorem ideleDefect_transversal (i : I) (w : WR) :
    dcl (κ σ).toAdd (r i) * dcl (i + (κ σ).toAdd) w =
      AdelicFunctoriality.ideleClassEquiv σ.toRingEquiv (dcl i w) *
        dcl (κ σ).toAdd (r (i + (k w).toAdd)) := by
  apply RelativeWeilGroup.inclusion_injective c F E
  have hσ := projection_transversal c F E κ r hr σ
  have hconj := RelativeWeilGroup.conjugation c F E (r (κ σ).toAdd) (dcl i w)
  rw [hσ] at hconj
  rw [map_mul, map_mul, ← hconj, inclusion_ideleDefect, inclusion_ideleDefect,
    inclusion_ideleDefect, inclusion_ideleDefect, hr, hr]
  simp only [toAdd_ofAdd]
  rw [show (κ σ).toAdd + i = i + (κ σ).toAdd from add_comm _ _,
    show i + (κ σ).toAdd + (k w).toAdd = (κ σ).toAdd + (i + (k w).toAdd) by abel]
  group

variable [Fintype I] [DecidableEq I] (b : ℕ) (η : I → HeckeCharacter E)

set_option hygiene false in
local notation "D" => ((I → DualGL b) ⋊[shiftAction k (DualGL b)] WR)
set_option hygiene false in
local notation "U" => ((I → BlockGL I b) ⋊[shiftAction k (BlockGL I b)] WR)
set_option hygiene false in
local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin b)

/-- The character recurrence of Clozel–Rajan (6.15), `η_(α+ι) ∘ σ = ω η_α`, where `ι` is
the label of `σ`. -/
def IsBlockRecurrence (ω : HeckeCharacter E) : Prop :=
  ∀ α : I, HeckeCharacter.comap σ.toRingEquiv (η (α + (κ σ).toAdd)) = ω * η α

/-- The dual automorphism `θ̂` translating the outer factors by the label of `σ`. -/
def dualShift (f : I → BlockGL I b) : I → BlockGL I b :=
  fun i => f (i + (κ σ).toAdd)

/-- The twisting element: in outer factor `i`, the block scalars `η_(α+ι)(ε_i)` times the
block relabelling by `ι`. -/
def twistingElement : I → BlockGL I b :=
  fun i => blockDiag b (fun α => sc (η (α + (κ σ).toAdd) (dcl (κ σ).toAdd (r i)))) *
    blockShift b (κ σ).toAdd

/-- The central element of `Ĝ` given by the Shapiro cocycle of `ω` at `w`. -/
def shapiroCentral (ω : HeckeCharacter E) (w : WR) : I → BlockGL I b :=
  fun i => Matrix.GeneralLinearGroup.scalar (Fin b × I) (shapiroCocycle c F E κ r hr ω w i)

theorem shiftedBlockEmbedding_left (x : D) (i : I) :
    (shiftedBlockEmbedding c F E κ r hr b η x).left i =
      blockDiag b (fun α => sc (η α (dcl i x.right)) * x.left (i - α)) := rfl

theorem shiftedBlockEmbedding_right (x : D) :
    (shiftedBlockEmbedding c F E κ r hr b η x).right = x.right := rfl

omit [Fintype I] [DecidableEq I] in
/-- Scalars pass through a single dual factor. -/
theorem scalar_mul_conj (A B C : ℂˣ) (h : DualGL b) :
    sc A * (sc B * h) * (sc C)⁻¹ = sc (A * B * C⁻¹) * h := by
  have hc : h * sc C⁻¹ = sc C⁻¹ * h := ((scalar_commute' b C⁻¹ h).eq).symm
  calc
    sc A * (sc B * h) * (sc C)⁻¹ = sc A * sc B * (h * sc C⁻¹) := by
      rw [← map_inv]
      simp only [mul_assoc]
    _ = sc A * sc B * (sc C⁻¹ * h) := by rw [hc]
    _ = sc (A * B * C⁻¹) * h := by
      rw [map_mul, map_mul]
      simp only [mul_assoc]

/-- The coordinate form of the twisted endoscopic condition. -/
theorem twistingElement_conj (ω : HeckeCharacter E)
    (hη : IsBlockRecurrence F E κ σ η ω) (x : D) (i : I) :
    twistingElement c F E κ r hr σ b η i *
        (shiftedBlockEmbedding c F E κ r hr b η x).left (i + (κ σ).toAdd) *
        (twistingElement c F E κ r hr σ b η (i + (k x.right).toAdd))⁻¹ =
      shapiroCentral c F E κ r hr b ω x.right i *
        (shiftedBlockEmbedding c F E κ r hr b η x).left i := by
  rw [shiftedBlockEmbedding_left, shiftedBlockEmbedding_left]
  simp only [twistingElement, shapiroCentral, shapiroCocycle, mul_inv_rev]
  rw [← blockDiag_scalar]
  have hP : ∀ (A B P : BlockGL I b) (d : I → DualGL b),
      A * P * blockDiag b d * (P⁻¹ * B) = A * (P * blockDiag b d * P⁻¹) * B := by
    intro A B P d
    simp only [mul_assoc]
  rw [hP, blockShift_conj_blockDiag, ← map_inv (blockDiag b), ← map_mul (blockDiag b),
    ← map_mul (blockDiag b), ← map_mul (blockDiag b)]
  congr 1
  funext α
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [show i + (κ σ).toAdd - (α + (κ σ).toAdd) = i - α by abel]
  have key : (η (α + (κ σ).toAdd)) (dcl (κ σ).toAdd (r i)) *
      (η (α + (κ σ).toAdd)) (dcl (i + (κ σ).toAdd) x.right) *
      ((η (α + (κ σ).toAdd)) (dcl (κ σ).toAdd (r (i + (k x.right).toAdd))))⁻¹ =
        ω (dcl i x.right) * (η α) (dcl i x.right) := by
    have hrec := congrArg (fun χ : HeckeCharacter E => χ (dcl i x.right)) (hη α)
    change (η (α + (κ σ).toAdd))
        (AdelicFunctoriality.ideleClassEquiv σ.toRingEquiv (dcl i x.right)) =
      ω (dcl i x.right) * (η α) (dcl i x.right) at hrec
    rw [← hrec, ← map_mul (η (α + (κ σ).toAdd)), ← map_inv (η (α + (κ σ).toAdd)),
      ← map_mul (η (α + (κ σ).toAdd)), ideleDefect_transversal c F E κ r hr σ i x.right,
      mul_inv_cancel_right]
  rw [scalar_mul_conj, key, map_mul, mul_assoc]

/-- On the dual group of the endoscopic group, the condition says that the image of `ξ₀`
lies in the twisted centralizer of the twisting element. -/
theorem twistingElement_conj_dual (ω : HeckeCharacter E)
    (hη : IsBlockRecurrence F E κ σ η ω) (h : I → DualGL b) (i : I) :
    twistingElement c F E κ r hr σ b η i *
        (shiftedBlockEmbedding c F E κ r hr b η ⟨h, 1⟩).left (i + (κ σ).toAdd) *
        (twistingElement c F E κ r hr σ b η i)⁻¹ =
      (shiftedBlockEmbedding c F E κ r hr b η ⟨h, 1⟩).left i := by
  have e := twistingElement_conj c F E κ r hr σ b η ω hη ⟨h, 1⟩ i
  simp only [map_one, toAdd_one', add_zero, shapiroCentral, shapiroCocycle, ideleDefect_one,
    one_mul] at e
  exact e

/-- The twisted endoscopic condition (E5): for every `x`,
`s · θ̂(ξ₀(x)) · s⁻¹ = a(w) · ξ₀(x)` in the semidirect product, where `w` is the Weil
component of `x`, `s` is the twisting element, `θ̂` is the outer translation by the label of
`σ` and `a` is the Shapiro cocycle of `ω`. -/
theorem twistedEndoscopicCondition (ω : HeckeCharacter E)
    (hη : IsBlockRecurrence F E κ σ η ω) (x : D) :
    ((⟨twistingElement c F E κ r hr σ b η, 1⟩ : U) *
        ⟨dualShift F E κ σ b (shiftedBlockEmbedding c F E κ r hr b η x).left,
          (shiftedBlockEmbedding c F E κ r hr b η x).right⟩ *
        (⟨twistingElement c F E κ r hr σ b η, 1⟩ : U)⁻¹ : U) =
      ⟨shapiroCentral c F E κ r hr b ω x.right * (shiftedBlockEmbedding c F E κ r hr b η x).left,
        (shiftedBlockEmbedding c F E κ r hr b η x).right⟩ := by
  apply SemidirectProduct.ext
  · funext i
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, inv_one, map_one, one_mul, MulAut.one_apply, Pi.mul_apply, Pi.inv_apply, shiftAction_apply, dualShift,
      shiftedBlockEmbedding_right]
    exact twistingElement_conj c F E κ r hr σ b η ω hη x i
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, inv_one, one_mul,
      mul_one]

end Relative

end Langlands.TraceFormula.CyclicBlockSum
