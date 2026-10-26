import Langlands.Representation.MatrixCoefficient.CentralL2
import Langlands.Representation.Unitary.HermitianDual

/-!
# Actual coefficient embeddings into the central L2 model

The actual coefficient function is restricted to the published central L2
subrepresentation, and its integral form is pulled back along the injection.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

namespace UnitaryCentralCharacter

variable (c : UnitaryCentralCharacter ρ)
  (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V)
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsMulRightInvariant]
  (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ)

/-- Restrict the actual coefficient function to the central L2 subrepresentation. -/
def coefficientL2Intertwiner :
    ρ.IntertwiningMap (Induction.centralL2Representation c.character c.norm_eq_one μ) where
  toLinearMap :=
    { toFun := fun v =>
        ⟨c.coefficientIntertwiner hρ ℓ v,
          (c.coefficientIntertwiner_memLp_iff hρ ℓ v μ 2).mpr (hL2 v)⟩
      map_add' v w := Subtype.ext ((c.coefficientIntertwiner hρ ℓ).map_add v w)
      map_smul' a v := Subtype.ext ((c.coefficientIntertwiner hρ ℓ).map_smul a v) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining
      ρ (Induction.centralInduced c.character) (c.coefficientIntertwiner hρ ℓ) g v

@[simp]
theorem coefficientL2Intertwiner_val (v : V) :
    (c.coefficientL2Intertwiner hρ ℓ μ hL2 v).1 =
      c.coefficientIntertwiner hρ ℓ v := rfl

/-- Inclusion recovers the original smooth central coefficient function. -/
@[simp]
theorem coefficientL2Intertwiner_inclusion (v : V) :
    Induction.centralL2Inclusion c.character c.norm_eq_one μ
        (c.coefficientL2Intertwiner hρ ℓ μ hL2 v) =
      c.coefficientIntertwiner hρ ℓ v := rfl

@[simp]
theorem coefficientL2Intertwiner_eval (v : V) (g : G) :
    Induction.eval _ _ (c.coefficientL2Intertwiner hρ ℓ μ hL2 v).1 g =
      matrixCoefficient ρ ℓ v g := rfl

/-- Evaluation at the identity still recovers the original functional. -/
@[simp]
theorem coefficientL2Intertwiner_eval_one (v : V) :
    Induction.eval _ _ (c.coefficientL2Intertwiner hρ ℓ μ hL2 v).1 1 = ℓ v :=
  c.coefficientIntertwiner_eval_one hρ ℓ v

/-- A nonzero coefficient functional makes the restricted map nonzero. -/
theorem coefficientL2Intertwiner_ne_zero (hℓ : ℓ ≠ 0) :
    c.coefficientL2Intertwiner hρ ℓ μ hL2 ≠ 0 := by
  intro hz
  apply c.coefficientIntertwiner_ne_zero hρ ℓ hℓ
  ext v g
  have hv := congrArg (fun f : ρ.IntertwiningMap
      (Induction.centralL2Representation c.character c.norm_eq_one μ) =>
        Induction.eval _ _ (f v).1 g) hz
  exact hv

/-- Irreducibility and a nonzero functional give an actual injection. -/
theorem coefficientL2Intertwiner_injective [Representation.IsIrreducible ρ]
    (hℓ : ℓ ≠ 0) :
    Function.Injective (c.coefficientL2Intertwiner hρ ℓ μ hL2) := by
  intro v w hvw
  apply c.coefficientIntertwiner_injective hρ ℓ hℓ
  exact congrArg Subtype.val hvw

variable [μ.IsHaarMeasure]

/-- Pull back the actual quotient-integral form along the coefficient injection. -/
def coefficientL2Form [Representation.IsIrreducible ρ] (hℓ : ℓ ≠ 0) :
    InvariantPositiveForm ρ :=
  (Induction.centralL2Form c.character c.norm_eq_one μ).comap
    (c.coefficientL2Intertwiner hρ ℓ μ hL2)
    (c.coefficientL2Intertwiner_injective hρ ℓ μ hL2 hℓ)

/-- The pulled-back form has the exact integral pairing of the actual
centrally covariant coefficient functions. -/
theorem coefficientL2Form_inner [Representation.IsIrreducible ρ]
    (hℓ : ℓ ≠ 0) (v w : V) :
    (c.coefficientL2Form hρ ℓ μ hL2 hℓ).inner v w =
      ∫ q, Induction.centralPairing c.character c.norm_eq_one
        (c.coefficientIntertwiner hρ ℓ v) (c.coefficientIntertwiner hρ ℓ w) q ∂μ :=
  rfl

/-- Its diagonal is exactly the integral of the descended coefficient norm square. -/
theorem coefficientL2Form_inner_self [Representation.IsIrreducible ρ]
    (hℓ : ℓ ≠ 0) (v : V) :
    (c.coefficientL2Form hρ ℓ μ hL2 hℓ).inner v v =
      ((∫ q, (c.coefficientNorm ℓ v q) ^ 2 ∂μ : ℝ) : ℂ) := by
  change (Induction.centralL2Form c.character c.norm_eq_one μ).inner
    (c.coefficientL2Intertwiner hρ ℓ μ hL2 v)
    (c.coefficientL2Intertwiner hρ ℓ μ hL2 v) = _
  rw [Induction.centralL2Form_inner_self]
  rw [coefficientL2Intertwiner_val, coefficientIntertwiner_norm]

end UnitaryCentralCharacter

namespace InvariantPositiveForm

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
/-- Positivity supplies a nonzero smooth-dual functional from a nonzero smooth carrier. -/
theorem exists_nonzero_smoothDual [Nontrivial V] (b : InvariantPositiveForm ρ)
    (hρ : IsSmooth ρ) :
    ∃ ℓ : SmoothDual ρ, ℓ.val ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨b.toSmoothDual hρ v, ?_⟩
  intro hz
  apply hv
  apply b.toSmoothDual_injective hρ
  exact (Subtype.ext hz).trans (map_zero (b.toSmoothDual hρ)).symm

end InvariantPositiveForm

/-- The analytic square-integrability hypothesis provides an actual injective
coefficient map into its central L2 model; no embedding certificate is assumed. -/
theorem IsSquareIntegrableModCenter.exists_coefficientL2_embedding
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [Representation.IsIrreducible ρ]
    (hsq : IsSquareIntegrableModCenter ρ μ) (hu : IsUnitarizable ρ) :
    ∃ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ)
      (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ),
      ℓ.val ≠ 0 ∧ Function.Injective (c.coefficientL2Intertwiner hsq.1.1 ℓ.val μ hL2) := by
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨b⟩ := hu
  obtain ⟨ℓ, hℓ⟩ := b.exists_nonzero_smoothDual hsq.1.1
  obtain ⟨_, c, hc⟩ := hsq
  exact ⟨c, ℓ, hc ℓ, hℓ, c.coefficientL2Intertwiner_injective _ _ _ _ hℓ⟩

end Langlands
