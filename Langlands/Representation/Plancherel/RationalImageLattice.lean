import Langlands.Representation.Plancherel.RationalImageCharacters
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite freeness of the actual rational-character valuation image

The generic finiteness premise concerns the actual rational-character module;
the published character-lattice theorem discharges it for connected reductive
groups. The image remains the range of the published valuation homomorphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Inclusion of the actual additive valuation image in the integer linear dual. -/
def rationalImageIntegerDual :
    Additive (rationalDiscreteValuationImage G) →ₗ[ℤ]
      (GroupScheme.rationalCharacters G →ₗ[ℤ] ℤ) :=
  (show Additive (rationalDiscreteValuationImage G) →+
      (GroupScheme.rationalCharacters G →ₗ[ℤ] ℤ) from
    { toFun := fun a => a.toMul.val.toAdd.toIntLinearMap
      map_zero' := rfl
      map_add' := fun _ _ => rfl }).toIntLinearMap

@[simp]
theorem rationalImageIntegerDual_apply (a : rationalDiscreteValuationImage G)
    (χ : GroupScheme.rationalCharacters G) :
    rationalImageIntegerDual G (Additive.ofMul a) χ = a.val.toAdd χ := rfl

theorem rationalImageIntegerDual_injective :
    Function.Injective (rationalImageIntegerDual G) := by
  intro a b h
  change a.toMul = b.toMul
  apply Subtype.ext
  change a.toMul.val.toAdd = b.toMul.val.toAdd
  apply AddMonoidHom.ext
  intro χ
  exact DFunLike.congr_fun h χ

/-- The actual valuation image has no integer torsion, without a finiteness premise. -/
instance rationalImage_isTorsionFree :
    Module.IsTorsionFree ℤ (Additive (rationalDiscreteValuationImage G)) :=
  (rationalImageIntegerDual_injective G).moduleIsTorsionFree
    (rationalImageIntegerDual G) (rationalImageIntegerDual G).map_smul

/-- The rank of the actual image; no equality with a split-center rank is asserted. -/
abbrev rationalImageRank : ℕ :=
  Module.finrank ℤ (Additive (rationalDiscreteValuationImage G))

section FiniteCharacters

variable [Module.Finite ℤ (GroupScheme.rationalCharacters G)]

/-- Finite generation of the character module implies finite generation of the
actual valuation image by the Noetherian property of its integer dual. -/
instance rationalImage_moduleFinite :
    Module.Finite ℤ (Additive (rationalDiscreteValuationImage G)) :=
  Module.Finite.of_injective (rationalImageIntegerDual G)
    (rationalImageIntegerDual_injective G)

/-- A chosen integer basis of the actual image, conditional on character finiteness. -/
def rationalImageBasis :
    Module.Basis (Fin (rationalImageRank G)) ℤ
      (Additive (rationalDiscreteValuationImage G)) :=
  Module.finBasis ℤ _

variable {B : Type v} [CommGroup B] [TopologicalSpace B]

/-- Reconstruct a character from its values on the chosen integer basis. -/
def rationalImageCharacterOfCoordinates (c : Fin (rationalImageRank G) → B) :
    rationalDiscreteValuationImage G →ₜ* B where
  toFun a :=
    ((rationalImageBasis G).constr ℤ (fun i => Additive.ofMul (c i))
      (Additive.ofMul a)).toMul
  map_one' := by
    change (((rationalImageBasis G).constr ℤ (fun i => Additive.ofMul (c i)))
      (0 : Additive (rationalDiscreteValuationImage G))).toMul = 1
    rw [map_zero]
    rfl
  map_mul' a b := by
    change (((rationalImageBasis G).constr ℤ (fun i => Additive.ofMul (c i)))
      (Additive.ofMul a + Additive.ofMul b)).toMul = _
    rw [map_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem rationalImageCharacterOfCoordinates_basis
    (c : Fin (rationalImageRank G) → B) (i : Fin (rationalImageRank G)) :
    rationalImageCharacterOfCoordinates G c ((rationalImageBasis G i).toMul) = c i := by
  change (((rationalImageBasis G).constr ℤ (fun i => Additive.ofMul (c i)))
    (rationalImageBasis G i)).toMul = _
  rw [Module.Basis.constr_basis]
  rfl

/-- The evaluation of the reconstructed character is a finite Laurent monomial. -/
theorem rationalImageCharacterOfCoordinates_apply
    (c : Fin (rationalImageRank G) → B) (a : rationalDiscreteValuationImage G) :
    rationalImageCharacterOfCoordinates G c a =
      ∏ i, c i ^ ((rationalImageBasis G).repr (Additive.ofMul a) i) := by
  change (((rationalImageBasis G).constr ℤ (fun i => Additive.ofMul (c i)))
    (Additive.ofMul a)).toMul = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul]
  rfl

variable [IsTopologicalGroup B] [T2Space B]

/-- Basis evaluation identifies image characters with finite tuples. -/
def rationalImageCharacterCoordinates :
    (rationalDiscreteValuationImage G →ₜ* B) ≃*
      (Fin (rationalImageRank G) → B) where
  toFun χ i := χ ((rationalImageBasis G i).toMul)
  invFun := rationalImageCharacterOfCoordinates G
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro a
    have he := DFunLike.congr_fun
      ((rationalImageBasis G).constr_self ℤ χ.toMonoidHom.toAdditive.toIntLinearMap)
      (Additive.ofMul a)
    exact congrArg Additive.toMul he
  right_inv c := funext (rationalImageCharacterOfCoordinates_basis G c)
  map_mul' _ _ := rfl

/-- The finite-coordinate description preserves compact-open topologies. -/
def rationalImageCharacterContinuousCoordinates :
    (rationalDiscreteValuationImage G →ₜ* B) ≃ₜ*
      (Fin (rationalImageRank G) → B) where
  toMulEquiv := rationalImageCharacterCoordinates G
  continuous_toFun := continuous_pi fun i => continuous_eval_const ((rationalImageBasis G i).toMul)
  continuous_invFun := by
    apply (ContinuousMonoidHom.isClosedEmbedding_coe
      (A := rationalDiscreteValuationImage G) (B := B)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro a
    change Continuous (fun c : Fin (rationalImageRank G) → B =>
      rationalImageCharacterOfCoordinates G c a)
    simp_rw [rationalImageCharacterOfCoordinates_apply]
    exact continuous_finsetProd _ fun i _ =>
      (continuous_apply i).zpow _

@[simp]
theorem rationalImageCharacterContinuousCoordinates_apply
    (χ : rationalDiscreteValuationImage G →ₜ* B) (i : Fin (rationalImageRank G)) :
    rationalImageCharacterContinuousCoordinates G χ i =
      χ ((rationalImageBasis G i).toMul) := rfl

end FiniteCharacters

/-- The published rational-character lattice theorem discharges image finiteness
for every actual connected reductive group. -/
theorem rationalReductiveImage_free_finite (hG : GroupScheme.IsConnectedReductive G) :
    Module.Free ℤ (Additive (rationalDiscreteValuationImage G)) ∧
      Module.Finite ℤ (Additive (rationalDiscreteValuationImage G)) := by
  have := (GroupScheme.rationalCharacterLattice F G hG).2
  exact ⟨inferInstance, inferInstance⟩

/-- Complex coordinates on actual image characters of a connected reductive group. -/
def rationalReductiveImageCharacterCoordinates (hG : GroupScheme.IsConnectedReductive G) :
    rationalImageCharacters G ≃ₜ* (Fin (rationalImageRank G) → ℂˣ) := by
  letI := (GroupScheme.rationalCharacterLattice F G hG).2
  exact rationalImageCharacterContinuousCoordinates G

/-- Circle coordinates on the actual unitary image dual. -/
def rationalReductiveUnitaryImageCoordinates (hG : GroupScheme.IsConnectedReductive G) :
    rationalUnitaryImageCharacters G ≃ₜ* (Fin (rationalImageRank G) → Circle) := by
  letI := (GroupScheme.rationalCharacterLattice F G hG).2
  exact rationalImageCharacterContinuousCoordinates G

end Langlands.Plancherel
