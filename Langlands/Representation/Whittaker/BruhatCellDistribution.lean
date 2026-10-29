import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.Whittaker.Distribution

/-! # Distribution conventions on actual upper Bruhat cells -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open HarmonicAnalysis.Distribution Hecke.TestFunction

universe uR

variable (n : ℕ) (R : Type uR) [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] (w : Equiv.Perm (Fin (n + 1)))

/-- Translation by the actual upper-unipotent matrices, restricted to one cell. -/
def bruhatCellBiTranslate (u₁ u₂ : upperUnipotent (n + 1) R) :
    UpperBruhatCell (n + 1) R w ≃ₜ UpperBruhatCell (n + 1) R w where
  toFun g := ⟨u₁.val * g.val * u₂.val,
    mem_upperBruhatCell_mul (n + 1) R w
      (upperUnipotentInUpperTriangular (n + 1) R u₂)
      (mul_mem_upperBruhatCell (n + 1) R w
        (upperUnipotentInUpperTriangular (n + 1) R u₁) g.property)⟩
  invFun g := ⟨u₁.val⁻¹ * g.val * u₂.val⁻¹,
    mem_upperBruhatCell_mul (n + 1) R w
      (upperUnipotentInUpperTriangular (n + 1) R u₂⁻¹)
      (mul_mem_upperBruhatCell (n + 1) R w
        (upperUnipotentInUpperTriangular (n + 1) R u₁⁻¹) g.property)⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp]
theorem bruhatCellBiTranslate_val (u₁ u₂ : upperUnipotent (n + 1) R)
    (g : UpperBruhatCell (n + 1) R w) :
    (bruhatCellBiTranslate n R w u₁ u₂ g).val = u₁.val * g.val * u₂.val :=
  rfl

@[simp]
theorem bruhatCellBiTranslate_symm_val (u₁ u₂ : upperUnipotent (n + 1) R)
    (g : UpperBruhatCell (n + 1) R w) :
    ((bruhatCellBiTranslate n R w u₁ u₂).symm g).val =
      u₁.val⁻¹ * g.val * u₂.val⁻¹ :=
  rfl

@[simp]
theorem pullback_bruhatCellBiTranslate_apply (u₁ u₂ : upperUnipotent (n + 1) R)
    (f : SchwartzBruhat (UpperBruhatCell (n + 1) R w))
    (g : UpperBruhatCell (n + 1) R w) :
    pullback (bruhatCellBiTranslate n R w u₁ u₂) f g =
      f (bruhatCellBiTranslate n R w u₁ u₂ g) :=
  rfl

/-- Cellwise bi-equivariance with the same two positive character factors as globally. -/
def IsBiEquivariantBruhatCellDistribution (ψ : UnitaryAdditiveCharacter R)
    (D : Distribution (UpperBruhatCell (n + 1) R w)) : Prop :=
  ∀ (u₁ u₂ : upperUnipotent (n + 1) R)
    (f : SchwartzBruhat (UpperBruhatCell (n + 1) R w)),
    D (pullback (bruhatCellBiTranslate n R w u₁ u₂) f) =
      ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f

theorem isBiEquivariantBruhatCellDistribution_iff (ψ : UnitaryAdditiveCharacter R)
    (D : Distribution (UpperBruhatCell (n + 1) R w)) :
    IsBiEquivariantBruhatCellDistribution n R w ψ D ↔
      ∀ (u₁ u₂ : upperUnipotent (n + 1) R)
        (f : SchwartzBruhat (UpperBruhatCell (n + 1) R w)),
        D (pullback (bruhatCellBiTranslate n R w u₁ u₂) f) =
          ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f :=
  Iff.rfl

variable (hτ : Set.MapsTo (weylTransposeHomeomorph n R)
  (upperBruhatCell (n + 1) R w) (upperBruhatCell (n + 1) R w))

/-- Restriction of the actual transpose involution, given a proof of cell stability. -/
def bruhatCellWeylTranspose :
    UpperBruhatCell (n + 1) R w ≃ₜ UpperBruhatCell (n + 1) R w where
  toFun g := ⟨weylTransposeHomeomorph n R g.val, hτ g.property⟩
  invFun g := ⟨weylTransposeHomeomorph n R g.val, hτ g.property⟩
  left_inv g := Subtype.ext (weylTransposeHomeomorph_involutive n R g.val)
  right_inv g := Subtype.ext (weylTransposeHomeomorph_involutive n R g.val)
  continuous_toFun :=
    ((weylTransposeHomeomorph n R).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((weylTransposeHomeomorph n R).continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem bruhatCellWeylTranspose_val (g : UpperBruhatCell (n + 1) R w) :
    (bruhatCellWeylTranspose n R w hτ g).val =
      weylTransposeHomeomorph n R g.val :=
  rfl

@[simp]
theorem bruhatCellWeylTranspose_involutive (g : UpperBruhatCell (n + 1) R w) :
    bruhatCellWeylTranspose n R w hτ (bruhatCellWeylTranspose n R w hτ g) = g :=
  (bruhatCellWeylTranspose n R w hτ).left_inv g

/-- Invariance under the restricted actual transpose, with explicit cell stability. -/
def IsWeylTransposeInvariantBruhatCellDistribution
    (D : Distribution (UpperBruhatCell (n + 1) R w)) : Prop :=
  pushforward (bruhatCellWeylTranspose n R w hτ) D = D

theorem isWeylTransposeInvariantBruhatCellDistribution_iff
    (D : Distribution (UpperBruhatCell (n + 1) R w)) :
    IsWeylTransposeInvariantBruhatCellDistribution n R w hτ D ↔
      ∀ f : SchwartzBruhat (UpperBruhatCell (n + 1) R w),
        D (pullback (bruhatCellWeylTranspose n R w hτ) f) = D f := by
  constructor
  · intro h f
    exact congrArg (fun E : Distribution (UpperBruhatCell (n + 1) R w) => E f) h
  · intro h
    ext f
    exact h f

end Langlands.Whittaker
