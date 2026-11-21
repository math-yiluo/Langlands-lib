import Langlands.Geometry.FormalGroup.DrinfeldFrameFromLine
import Langlands.Geometry.FormalGroup.DrinfeldLubinTateFrobenius
import Langlands.Geometry.FormalGroup.DrinfeldScalarFrobeniusHeight
import Langlands.Galois.Local.SeparableUnramifiedCompletion

/-! # A fixed special formal division-order module of height d² -/

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

local instance fixedFrameLocalHom {L : Type u} [Field L] [Algebra K L] (i : L →ₐ[K] D) :
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
local notation "κ" => UnramifiedCompletion.Residue K

/-- Choose the residue embedding of the actual degree-d integer subfield into
 the residue field of the completed maximal unramified base. -/
def drinfeldFixedResidueEmbedding : ResidueField C →ₐ[𝓀[K]] κ := by
  let : Finite (ResidueField C) := subfieldResidueFinite emb hC
  let : IsAlgClosed κ := IsAlgClosure.isAlgClosed 𝓀[K]
  exact IsAlgClosed.lift

variable {π : 𝒪[K]} (hπ : Irreducible π)

/-- A fixed special formal division-order module over the completed unramified
 residue field, constructed from the standard Lubin–Tate line. -/
def drinfeldFixedFrame : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := emb) (R := κ) π := by
  let : Finite (ResidueField C) := subfieldResidueFinite emb hC
  let χ := drinfeldFixedResidueEmbedding K D hInv
  let j := drinfeldArithmeticUniformizer K D hInv hπ
  let hPow := drinfeldArithmeticUniformizer_pow K D hInv hπ
  let hComm := drinfeldArithmeticUniformizer_mul K D hInv hπ
  let hResidue := subfieldArithmeticFrobenius_sub_lt_one K D E emb hE
  let hp := DrinfeldResidue.exists_expChar_card K κ
  let p := hp.choose
  let e : ℕ := hp.choose_spec.choose
  let : ExpChar κ p := hp.choose_spec.choose_spec.2.1
  have hcard : Nat.card 𝓀[K] = p ^ e := hp.choose_spec.choose_spec.2.2
  let H := drinfeldLubinTateLine emb χ hC hπ
  let f := drinfeldLubinTateCoefficients emb χ hC hπ
  let t := drinfeldLubinTateFrobenius emb χ hC hπ p hcard σ hResidue
  let htPow := drinfeldLubinTateFrobenius_pow emb χ hC hπ p hcard σ hResidue
  let htComm := drinfeldLubinTateFrobenius_mul emb χ hC hπ p hcard σ hResidue
  let X := specialFrameFromLine hE emb hdegree H f t hπ j hPow hComm htPow htComm
    (fun _ => rfl) χ (drinfeldLubinTateCoefficients_linearCoeff emb χ hC hπ)
  refine ⟨X, hπ, ?_⟩
  change (H.copies (Fin d)).HasPiHeight π (Nat.card 𝓀[K]) (d ^ 2)
  have hPower := copies_scalarFrobenius (I := Fin d) H
    (drinfeldLubinTateLine_uniformizer_frobenius emb χ hC hπ p hcard)
  have hHeight := hasPiHeight_of_scalarFrobenius (H.copies (Fin d)) hcard
    (UnramifiedCompletion.residue_uniformizer K hπ) hPower (reducedDegree_pos K D)
  simpa only [Nat.card_fin, pow_two] using hHeight

end Langlands.FormalGroup.LocalDivision
