import Langlands.Geometry.FormalGroup.DrinfeldFixedFrame
import Langlands.Geometry.FormalGroup.DrinfeldLineRationalCentralizer
import Langlands.Geometry.FormalGroup.RationalCopyMatrices

/-! # The actual order action in the blocks of the fixed special frame -/

noncomputable section

namespace Langlands.FormalGroup

universe u v w

namespace ModuleLaw.RationalHom

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
  {F : Type w} [Field F] [Algebra O F] {I : Type} [Fintype I] [DecidableEq I]
  (M : ModuleLaw O R Unit)

/-- A product formal endomorphism with diagonal underlying group map has the
rationalizations of its factor maps as its diagonal blocks. -/
theorem copiesMatrixEquiv_ofHom_diagonal {z : Hom (M.copies I) (M.copies I)}
    (f : I → Hom M M) (hz : z.toHom = CommLaw.Hom.diagonal fun i => (f i).toHom) :
    copiesMatrixEquiv (F := F) M (ofHom z) = Matrix.diagonal (fun i => ofHom (f i)) := by
  apply Matrix.ext
  intro i j
  have hproj : (Hom.copyProjection M i).comp z = (f i).comp (Hom.copyProjection M i) := by
    apply Hom.ext
    change (CommLaw.Hom.copyProjection i).comp z.toHom = (f i).toHom.comp (CommLaw.Hom.copyProjection i)
    rw [hz]
    exact CommLaw.Hom.copyProjection_comp_diagonal (fun k => (f k).toHom) i
  rw [copiesMatrixEquiv_apply, copiesEntry, copyProjection, copyInclusion,
    ← ofHom_comp, ← ofHom_comp, ← Hom.comp_assoc, hproj, Hom.comp_assoc,
    Hom.copyProjection_comp_copyInclusion]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, Hom.comp_id, Matrix.diagonal_apply_eq]
  · rw [ite_eq_right hij, Hom.comp_zero, map_zero, Matrix.diagonal_apply_ne _ hij]

end ModuleLaw.RationalHom

namespace LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw
open Langlands.ClassFieldTheory.Local Langlands.LocalGalois.Separable
open Langlands.LocalGalois.Separable.UnramifiedCompletion
open _root_.Langlands.Brauer

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance fixedBlocksLocalHom {L : Type u} [Field L] [Algebra K L] (i : L →ₐ[K] D) :
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

local instance fixedBlocksFinite : Finite (ResidueField C) := subfieldResidueFinite emb hC

variable {π : 𝒪[K]} (hπ : Irreducible π)

/-- The single formal line used in the actual fixed frame, before taking its finite power. -/
abbrev drinfeldFixedLine : ModuleLaw 𝒪[K] κ Unit := drinfeldLubinTateLine emb χ hC hπ

local notation "H" => drinfeldFixedLine K D hInv hπ
local notation "Φ" => drinfeldFixedFrame K D hInv hπ
local notation "EndH" => ModuleLaw.RationalHom K H H
local notation "J" => drinfeldArithmeticUniformizer K D hInv hπ
local notation "hJ" => drinfeldArithmeticUniformizer_pow K D hInv hπ
local notation "j" => drinfeldIntegralUniformizer J hJ
local notation "hp" => DrinfeldResidue.exists_expChar_card K κ
local notation "p" => Classical.choose hp
local notation "hpdata" => Classical.choose_spec (Classical.choose_spec hp)
local notation "hcard" => And.right (And.right hpdata)

local instance fixedBlocksExpChar : ExpChar κ p := And.left (And.right hpdata)

/-- Project the rational scalar-linear endomorphisms of the actual frame to blocks. -/
def drinfeldFixedFrameBlockEquiv : RationalHom K (Φ).val.formalModule (Φ).val.formalModule ≃ₐ[K]
    Matrix (Fin d) (Fin d) EndH := RationalHom.copiesMatrixEquiv H

/-- The action of the actual division order, rationalized and written in blocks. -/
def drinfeldFixedOrderBlocks : IntegerRing K D →+* Matrix (Fin d) (Fin d) EndH :=
  (drinfeldFixedFrameBlockEquiv K D hInv hπ).toRingHom.comp
    (RationalHom.ofHomEnd.comp (Φ).val.order.action)

local notation "blocks" => drinfeldFixedOrderBlocks K D hInv hπ
local notation "rawf" => drinfeldLubinTateCoefficients emb χ hC hπ
local notation "rawt" => drinfeldLubinTateFrobenius emb χ hC hπ p hcard σ hσ
local notation "htPow" => drinfeldLubinTateFrobenius_pow emb χ hC hπ p hcard σ hσ
local notation "htComm" => drinfeldLubinTateFrobenius_mul emb χ hC hπ p hcard σ hσ
local notation "hfTangent" => drinfeldLubinTateCoefficients_linearCoeff emb χ hC hπ

/-- The embedded integers act diagonally through the inverse Frobenius twists of the line. -/
theorem drinfeldFixedOrderBlocks_coefficient (a : C) :
    blocks (subfieldIntegerInclusion K D emb a) = Matrix.diagonal
      (fun i : Fin d => drinfeldLineRationalCoefficient emb χ hC hπ ((τ⁻¹ ^ i.val) a)) := by
  change RationalHom.copiesMatrixEquiv H (RationalHom.ofHom ((Φ).val.order.action
    (subfieldIntegerInclusion K D emb a))) = Matrix.diagonal (fun i : Fin d =>
      RationalHom.ofHom (drinfeldLineCoefficientEnd emb χ hC hπ ((τ⁻¹ ^ i.val) a)))
  apply RationalHom.copiesMatrixEquiv_ofHom_diagonal
  exact specialFrameFromLine_coefficient hE emb hdegree H rawf rawt hπ J hJ
    (drinfeldArithmeticUniformizer_mul K D hInv hπ) htPow htComm (fun _ => rfl) χ hfTangent a

/-- The normalized division uniformizer has one arithmetic Frobenius on each diagonal block. -/
theorem drinfeldFixedOrderBlocks_uniformizer :
    blocks j = Matrix.scalar (Fin d) (drinfeldLineRationalFrobenius emb χ hC hπ p hcard σ hσ) := by
  change RationalHom.copiesMatrixEquiv H (RationalHom.ofHom ((Φ).val.order.action j)) =
    Matrix.diagonal (fun _ : Fin d => RationalHom.ofHom (drinfeldLineFrobeniusEnd emb χ hC hπ p hcard σ hσ))
  apply RationalHom.copiesMatrixEquiv_ofHom_diagonal
  exact specialFrameFromLine_uniformizer hE emb hdegree H rawf rawt hπ J hJ
    (drinfeldArithmeticUniformizer_mul K D hInv hπ) htPow htComm (fun _ => rfl) χ hfTangent

end LocalDivision
end Langlands.FormalGroup
