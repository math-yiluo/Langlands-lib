import Langlands.MathlibBase
import Langlands.Group.GL.Basic
import Langlands.Representation.Category.Twist

/-! # Unramified determinant twists -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ

variable {F : Type uF} [Field F] [ValuativeRel F]

/-- A quasicharacter of `Fˣ` is unramified when it is trivial on `𝒪[F]ˣ`. -/
def IsUnramifiedQuasicharacter (χ : Fˣ →* ℂˣ) : Prop :=
  ∀ u : 𝒪[F]ˣ, χ (Units.map 𝒪[F].subtype.toMonoidHom u) = 1

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Triviality on the integer units gives an open kernel. -/
theorem IsUnramifiedQuasicharacter.isOpen_ker {χ : Fˣ →* ℂˣ}
    (hχ : IsUnramifiedQuasicharacter χ) : IsOpen (χ.ker : Set Fˣ) := by
  let integerBall : Set F := 𝒪[F]
  have hball : IsOpen integerBall := Valuation.isOpen_integer (v := valuation F)
  have hopen : IsOpen (((↑) : Fˣ → F) ⁻¹' integerBall ∩
      (fun a : Fˣ => ((a⁻¹ : Fˣ) : F)) ⁻¹' integerBall) :=
    (hball.preimage Units.continuous_val).inter
      (hball.preimage (Units.continuous_val.comp continuous_inv))
  apply χ.ker.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · have hOne : (1 : F) ∈ integerBall := one_mem 𝒪[F]
    refine ⟨hOne, ?_⟩
    change ((((1 : Fˣ)⁻¹ : Fˣ) : F)) ∈ integerBall
    simpa only [inv_one, Units.val_one] using hOne
  · intro a ha
    let u : 𝒪[F]ˣ := ⟨⟨a, ha.1⟩, ⟨↑a⁻¹, ha.2⟩,
      Subtype.ext a.val_inv, Subtype.ext a.inv_val⟩
    have hu : Units.map 𝒪[F].subtype.toMonoidHom u = a := Units.ext rfl
    exact MonoidHom.mem_ker.mpr (hu ▸ hχ u)

/-- The determinant pullback of an unramified quasicharacter has open kernel. -/
theorem IsUnramifiedQuasicharacter.isOpen_ker_det {χ : Fˣ →* ℂˣ}
    (hχ : IsUnramifiedQuasicharacter χ) (n : ℕ) :
    IsOpen ((χ.comp (GeneralLinear.determinant (n := n))).ker : Set (GeneralLinear n F)) :=
  hχ.isOpen_ker.preimage GeneralLinear.determinantContinuous.continuous

/-- The smooth twist `π ⊗ (χ ∘ det)` of BK93 (6.2.3) and (6.2.5). -/
def unramifiedTwist {n : ℕ} (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (χ : Fˣ →* ℂˣ) (hχ : IsUnramifiedQuasicharacter χ) :
    SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F) :=
  SmoothRep.twist (χ.comp GeneralLinear.determinant) (hχ.isOpen_ker_det n) π

end Langlands.BushnellKutzko
