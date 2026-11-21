import Langlands.Geometry.FormalGroup.DrinfeldFixedFrameBlocks
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrame
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Ring.Action.ConjAct

/-! # Matrix coordinates on the actual rational automorphisms of the fixed frame -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw
open Langlands.ClassFieldTheory.Local Langlands.LocalGalois.Separable
open Langlands.LocalGalois.Separable.UnramifiedCompletion
open _root_.Langlands.Brauer

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance fixedMatricesLocalHom {L : Type u} [Field L] [Algebra K L] (i : L →ₐ[K] D) :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D i)) := subfieldIntegerAlgebra_isLocalHom i

variable (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
  reciprocalClass (CentralSimple.reducedDegree K D))

local notation "d" => CentralSimple.reducedDegree K D
local notation "E" => drinfeldUnramifiedField K D
local notation "hE" => drinfeldUnramifiedField_unramified K D
local notation "hdegree" => drinfeldUnramifiedField_degree K D
local notation "emb" => drinfeldUnramifiedEmbedding K D hInv
local notation "C" => SubfieldIntegerRing K D emb
local notation "hC" => drinfeldUnramifiedEmbedding_finiteEtale K D hInv
local notation "σ" => finiteUnramifiedFrobenius K E hE
local notation "τ" => subfieldIntegerFrobenius emb σ hC
local notation "hσ" => subfieldArithmeticFrobenius_sub_lt_one K D E emb hE
local notation "κ" => UnramifiedCompletion.Residue K
local notation "χ" => drinfeldFixedResidueEmbedding K D hInv

local instance fixedMatricesFinite : Finite (ResidueField C) := subfieldResidueFinite emb hC

variable {π : 𝒪[K]} (hπ : Irreducible π)

local notation "H" => drinfeldFixedLine K D hInv hπ
local notation "Φ" => drinfeldFixedFrame K D hInv hπ
local notation "EndH" => ModuleLaw.RationalHom K H H
local notation "I" => Fin d
local notation "J" => drinfeldArithmeticUniformizer K D hInv hπ
local notation "hJ" => drinfeldArithmeticUniformizer_pow K D hInv hπ
local notation "Πint" => drinfeldIntegralUniformizer J hJ
local notation "iC" => subfieldIntegerInclusion K D emb
local notation "hp" => DrinfeldResidue.exists_expChar_card K κ
local notation "p" => Classical.choose hp
local notation "hpdata" => Classical.choose_spec (Classical.choose_spec hp)
local notation "hcard" => And.right (And.right hpdata)

local instance fixedMatricesExpChar : ExpChar κ p := And.left (And.right hpdata)

local notation "S" => drinfeldLineRationalCentralizer emb χ hC hπ p hcard σ hσ
local notation "EndBlocks" => Matrix I I EndH
local notation "N" => SpecialModule.formalModule (Subtype.val Φ)
local notation "OAction" => SpecialModule.order (Subtype.val Φ)

private def fixedLineCoefficient : C →+* EndH := drinfeldLineRationalCoefficient emb χ hC hπ

private def fixedLineFrobenius : EndH := drinfeldLineRationalFrobenius emb χ hC hπ p hcard σ hσ

private def fixedLineFrobeniusUnit : EndHˣ :=
  drinfeldLineRationalFrobeniusUnit emb χ hC hπ p hcard σ hσ

local notation "f" => fixedLineCoefficient K D hInv hπ
local notation "t" => fixedLineFrobenius K D hInv hπ
local notation "uFrob" => fixedLineFrobeniusUnit K D hInv hπ

private theorem fixedLineFrobeniusUnit_val : (uFrob).val = t :=
  drinfeldLineRationalFrobeniusUnit_val emb χ hC hπ p hcard σ hσ

private theorem fixedLineFrobenius_pow_mul (n : ℕ) (a : C) :
    t ^ n * f a = f ((τ ^ n) a) * t ^ n :=
  drinfeldLineRationalFrobenius_pow_mul emb χ hC hπ p hcard σ hσ n a

private def fixedFrameFrobeniusDiagonal : EndBlocksˣ :=
  Units.map (Matrix.diagonalRingHom I EndH).toMonoidHom
    (MulEquiv.piUnits.symm (fun i : I => uFrob ^ i.val))

/-- Conjugate the frame's block matrix by the powers of arithmetic Frobenius on the diagonal. -/
def drinfeldFixedFrameUntwist : EndBlocks ≃ₐ[K] EndBlocks :=
  MulSemiringAction.toAlgEquiv K EndBlocks (ConjAct.toConjAct (fixedFrameFrobeniusDiagonal K D hInv hπ))

/-- Rational block coordinates after conjugating the coefficient twists to the same line action. -/
def drinfeldFixedFrameNormalizedBlocks : RationalHom K N N ≃ₐ[K] EndBlocks :=
  (drinfeldFixedFrameBlockEquiv K D hInv hπ).trans (drinfeldFixedFrameUntwist K D hInv hπ)

local notation "normE" => drinfeldFixedFrameNormalizedBlocks K D hInv hπ
local notation "untwist" => drinfeldFixedFrameUntwist K D hInv hπ

/-- The order action expressed in the normalized block coordinates. -/
def drinfeldFixedOrderNormalizedBlocks : IntegerRing K D →+* EndBlocks :=
  (untwist).toRingHom.comp (drinfeldFixedOrderBlocks K D hInv hπ)

local notation "normOrd" => drinfeldFixedOrderNormalizedBlocks K D hInv hπ

private theorem fixedOrderNormalized_apply (a : IntegerRing K D) :
    normOrd a = normE (RationalHom.ofHom ((OAction).action a)) := rfl

private theorem untwist_diagonal (v : I → EndH) :
    untwist (Matrix.diagonal v) = Matrix.diagonal
      (fun i : I => (Units.val (uFrob ^ i.val) : EndH) * v i * Units.val ((uFrob ^ i.val)⁻¹)) := by
  change Matrix.diagonal (fun i : I => (Units.val (uFrob ^ i.val) : EndH)) * Matrix.diagonal v *
    Matrix.diagonal (fun i : I => (Units.val ((uFrob ^ i.val)⁻¹) : EndH)) = _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]

private theorem fixedOrderNormalized_coefficient (a : C) : normOrd (iC a) = Matrix.scalar I (f a) := by
  change untwist (drinfeldFixedOrderBlocks K D hInv hπ (iC a)) = _
  have hb : drinfeldFixedOrderBlocks K D hInv hπ (iC a) = Matrix.diagonal
      (fun i : I => f ((τ⁻¹ ^ i.val) a)) := drinfeldFixedOrderBlocks_coefficient K D hInv hπ a
  rw [hb, untwist_diagonal, Matrix.scalar_apply]
  apply congrArg Matrix.diagonal
  funext i
  have hcancel : (τ ^ i.val) ((τ⁻¹ ^ i.val) a) = a := by
    rw [← AlgEquiv.mul_apply, inv_pow, mul_inv_cancel, AlgEquiv.one_apply]
  have hs : (Units.val (uFrob ^ i.val) : EndH) * f ((τ⁻¹ ^ i.val) a) = f a * Units.val (uFrob ^ i.val) := by
    simpa only [Units.val_pow_eq_pow_val, fixedLineFrobeniusUnit_val, hcancel] using
      fixedLineFrobenius_pow_mul K D hInv hπ i.val ((τ⁻¹ ^ i.val) a)
  rw [hs, mul_assoc, Units.mul_inv, mul_one]

private theorem fixedOrderNormalized_uniformizer : normOrd Πint = Matrix.scalar I t := by
  change untwist (drinfeldFixedOrderBlocks K D hInv hπ Πint) = _
  have hb : drinfeldFixedOrderBlocks K D hInv hπ Πint = Matrix.scalar I t :=
    drinfeldFixedOrderBlocks_uniformizer K D hInv hπ
  rw [hb]
  simp only [Matrix.scalar_apply, untwist_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  have hs : Commute (Units.val (uFrob ^ i.val) : EndH) t := by
    simpa only [Units.val_pow_eq_pow_val, fixedLineFrobeniusUnit_val] using (Commute.refl t).pow_left i.val
  rw [hs.eq, mul_assoc, Units.mul_inv, mul_one]

private theorem commute_scalar_entries (Z : EndBlocks) (a : EndH) :
    Commute Z (Matrix.scalar I a) ↔ ∀ i j, Commute (Z i j) a := by
  rw [Matrix.scalar_apply]
  constructor
  · intro h i j
    have he := congrArg (fun W : EndBlocks => W i j) h.eq
    change (Z * Matrix.diagonal (fun _ => a) : EndBlocks) i j =
      (Matrix.diagonal (fun _ => a) * Z : EndBlocks) i j at he
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  · intro h
    show Z * Matrix.diagonal (fun _ => a) = Matrix.diagonal (fun _ => a) * Z
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact (h i j).eq

/-- In normalized block coordinates, the commutation equations for the full
order are the line's two commutation equations on every entry. -/
theorem drinfeldFixedFrameNormalizedBlocks_centralizer (Z : EndBlocks) :
    (∀ a : IntegerRing K D, Commute Z (normOrd a)) ↔ ∀ i j, Z i j ∈ S := by
  constructor
  · intro h i k
    apply (mem_drinfeldLineRationalCentralizer emb χ hC hπ p hcard σ hσ _).mpr
    refine ⟨fun a => ?_, ?_⟩
    · have hc := h (iC a)
      rw [fixedOrderNormalized_coefficient] at hc
      exact (commute_scalar_entries K D hInv hπ Z _).mp hc i k
    · have ht := h Πint
      rw [fixedOrderNormalized_uniformizer] at ht
      exact (commute_scalar_entries K D hInv hπ Z _).mp ht i k
  · intro h a
    have hc (b : C) : Commute Z (normOrd (iC b)) := by
      rw [fixedOrderNormalized_coefficient]
      apply (commute_scalar_entries K D hInv hπ Z _).mpr
      intro i k
      exact ((mem_drinfeldLineRationalCentralizer emb χ hC hπ p hcard σ hσ _).mp (h i k)).1 b
    have ht : Commute Z (normOrd Πint) := by
      rw [fixedOrderNormalized_uniformizer]
      apply (commute_scalar_entries K D hInv hπ Z _).mpr
      intro i k
      exact ((mem_drinfeldLineRationalCentralizer emb χ hC hπ p hcard σ hσ _).mp (h i k)).2
    let horder := (finiteUnramifiedFrobenius_orderOf K E hE).trans hdegree
    let hconj := drinfeldArithmeticUniformizer_mul K D hInv hπ
    let coords := integerCyclicCoordinates K D E hE emb hdegree hπ hJ horder hconj
    have hsum : a = ∑ i : I, iC (coords a i) * Πint ^ i.val := by
      have he := integerCyclicCoordinates_symm_apply E hE emb hdegree hπ hJ horder hconj (coords a)
      change coords.symm (coords a) = _ at he
      rwa [Equiv.symm_apply_apply] at he
    rw [hsum, map_sum]
    apply Commute.sum_right
    intro i _
    rw [map_mul (normOrd), map_pow (normOrd)]
    exact (hc _).mul_right (ht.pow_right _)

private def fixedMatrixScalarMap : Matrix I I K →ₐ[K] ModuleLaw.OrderAction.RationalHom K OAction OAction := by
  let fmat : Matrix I I K →ₐ[K] EndBlocks := (Algebra.ofId K EndH).mapMatrix
  let raw : Matrix I I K →ₐ[K] RationalHom K N N := (normE).symm.toAlgHom.comp fmat
  have hcomm (A : Matrix I I K) : ∀ a : IntegerRing K D, Commute (raw A)
      (RationalHom.ofHom ((OAction).action a)) := by
    have h := (drinfeldFixedFrameNormalizedBlocks_centralizer K D hInv hπ (fmat A)).mpr (fun i j => by
      change algebraMap K EndH (A i j) ∈ S
      exact (S).algebraMap_mem _)
    intro a
    have ha := (h a).map (normE).symm.toAlgHom
    rw [fixedOrderNormalized_apply] at ha
    change Commute ((normE).symm (fmat A)) (RationalHom.ofHom ((OAction).action a))
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using ha
  exact
    { toFun := fun A => ⟨raw A, fun a => (hcomm A a).eq⟩
      map_zero' := ModuleLaw.OrderAction.RationalHom.ext raw.map_zero
      map_one' := ModuleLaw.OrderAction.RationalHom.ext raw.map_one
      map_add' := fun A B => ModuleLaw.OrderAction.RationalHom.ext (raw.map_add A B)
      map_mul' := fun A B => ModuleLaw.OrderAction.RationalHom.ext (raw.map_mul A B)
      commutes' := fun a => ModuleLaw.OrderAction.RationalHom.ext (raw.commutes a) }

private theorem fixedMatrixScalarMap_entry (A : Matrix I I K) (i j : I) :
    normE (fixedMatrixScalarMap K D hInv hπ A).val i j = algebraMap K EndH (A i j) := by
  change normE ((normE).symm ((Algebra.ofId K EndH).mapMatrix A)) i j = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- Actual matrix coordinates for the rational full-order endomorphisms of the fixed frame. -/
def drinfeldFixedFrameMatrixCoordinates : (Φ).val.MatrixCoordinates := by
  let scalar := fixedMatrixScalarMap K D hInv hπ
  refine AlgEquiv.ofBijective scalar ⟨?_, ?_⟩
  · intro A B h
    apply Matrix.ext
    intro i j
    have he := congrArg (fun z : ModuleLaw.OrderAction.RationalHom K OAction OAction =>
      normE z.val i j) h
    change normE (fixedMatrixScalarMap K D hInv hπ A).val i j =
      normE (fixedMatrixScalarMap K D hInv hπ B).val i j at he
    rw [fixedMatrixScalarMap_entry, fixedMatrixScalarMap_entry] at he
    exact drinfeldLineRationalScalar_injective emb χ hC hπ p hcard he
  · intro z
    let Z := normE z.val
    have hZ : ∀ i j, Z i j ∈ S :=
      (drinfeldFixedFrameNormalizedBlocks_centralizer K D hInv hπ Z).mp (fun a => by
        rw [fixedOrderNormalized_apply]
        exact (show Commute z.val (RationalHom.ofHom ((OAction).action a)) from z.commutes a).map (normE).toAlgHom)
    let equiv := drinfeldLineRationalScalarEndEquiv emb χ hC hπ p hcard σ hσ
    let A : Matrix I I K := Matrix.of (fun i j => equiv.symm ⟨Z i j, hZ i j⟩)
    refine ⟨A, ModuleLaw.OrderAction.RationalHom.ext ?_⟩
    apply (normE).injective
    apply Matrix.ext
    intro i j
    change normE (fixedMatrixScalarMap K D hInv hπ A).val i j = Z i j
    rw [fixedMatrixScalarMap_entry]
    exact congrArg Subtype.val (equiv.apply_symm_apply ⟨Z i j, hZ i j⟩)

/-- The matrix coordinates send each scalar matrix to its scalar entries in the normalized blocks. -/
theorem drinfeldFixedFrameMatrixCoordinates_entry (A : Matrix I I K) (i j : I) :
    normE (drinfeldFixedFrameMatrixCoordinates K D hInv hπ A).val i j =
      algebraMap K EndH (A i j) := fixedMatrixScalarMap_entry K D hInv hπ A i j

end Langlands.FormalGroup.LocalDivision
