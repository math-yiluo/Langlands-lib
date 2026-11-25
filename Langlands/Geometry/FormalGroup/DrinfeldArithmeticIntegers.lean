import Langlands.Geometry.FormalGroup.DrinfeldArithmeticSubfield
import Langlands.Geometry.FormalGroup.DrinfeldDeligneResidueComparisonStatement
import Langlands.Galois.Local.SeparableUnramifiedIntegerLift

/-! # Integer comparison for Drinfeld's arithmetic unramified subfield -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel IsLocalRing CentralDivision CentralSimple
open Langlands.LocalGalois Langlands.LocalGalois.Separable Langlands.ClassFieldTheory.Local
open Langlands.GroupScheme.Descent.FiniteUnramified
open _root_.Langlands.Brauer
open scoped WithZero

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance arithmeticIntegersNormedField : NontriviallyNormedField K := localNormedField K
local instance arithmeticIntegersComplete : CompleteSpace K := localNormedField_complete K
local instance arithmeticIntegersUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance arithmeticIntegersUnramifiedAlgebra : Algebra ↥𝒪[K] (fixedFieldIntegers K) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation K) (vA := fixedFieldValuation K)

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
  (ι : E →ₐ[K] D)

omit [FiniteDimensional K E] in
/-- The restricted division valuation and the spectral valuation induce the same order. -/
theorem subfieldSpectralValuation_le_iff (x y : E) :
    spectralValuation K E x ≤ spectralValuation K E y ↔
      localDivisionSubfieldValuation K D ι x ≤ localDivisionSubfieldValuation K D ι y := by
  let := localDivisionSubfieldNormedField K D ι
  let := localDivisionSubfieldNormedAlgebra K D ι
  change spectralNorm K E x ≤ spectralNorm K E y ↔ _
  simpa only [NormedAlgebra.norm_eq_spectralNorm K] using
    localDivisionSubfield_norm_le_iff K D ι x y

/-- The restricted division integers of the embedded field are the actual
spectral integers of the same field, by the identity on underlying elements. -/
def subfieldSpectralIntegerEquiv : SubfieldIntegerRing K D ι ≃+* extensionIntegers K E where
  toFun x := ⟨x.val, by
    change spectralValuation K E (x : E) ≤ 1
    rw [← map_one (spectralValuation K E), subfieldSpectralValuation_le_iff K D E ι, map_one]
    exact x.property⟩
  invFun x := ⟨x.val, by
    change localDivisionSubfieldValuation K D ι (x : E) ≤ 1
    rw [← map_one (localDivisionSubfieldValuation K D ι), ← subfieldSpectralValuation_le_iff K D E ι, map_one]
    exact x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Identify the embedded integer ring with the original coefficient
subalgebra in the maximal unramified integers. -/
def subfieldUnramifiedIntegerEquiv (hE : E ≤ inertiaFixedField K) :
    SubfieldIntegerRing K D ι ≃ₐ[𝒪[K]] integerCoefficients K E :=
  { (subfieldSpectralIntegerEquiv K D E ι).trans (integerCoefficientsEquiv K E hE).symm with
    commutes' := fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl)) }

/-- A degree-d embedded arithmetic-unramified stage gives the finite étale
integer subfield required by the special formal module definition. -/
theorem subfieldArithmeticUnramifiedOfReducedDegree (hE : ArithmeticUnramified K E)
    (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D) :
    IsUnramifiedSubfieldOfReducedDegree K D ι := by
  have hle := ((separableUnramified K).1 E).mpr hE
  let : Algebra.Etale 𝒪[K] (integerCoefficients K E) := integerCoefficients_etale K E hle
  exact ⟨inferInstance, localDivisionSubfieldInteger_finite K D ι,
    Algebra.Etale.of_equiv (subfieldUnramifiedIntegerEquiv K D E ι hle).symm, hdegree⟩

variable [IsGalois K E]

/-- Arithmetic Frobenius in the original embedded integers has the strict
valuation formula expressing the residue cardinality power. -/
theorem subfieldArithmeticFrobenius_sub_lt_one (hE : ArithmeticUnramified K E)
    (a : SubfieldIntegerRing K D ι) :
    localReducedNormIntValuation K D
      (ι (finiteUnramifiedFrobenius K E hE (a : E)) - ι ((a : E) ^ Nat.card 𝓀[K])) < 1 := by
  let s := finiteUnramifiedFrobenius K E hE
  let b := subfieldSpectralIntegerEquiv K D E ι a
  let C := extensionIntegers K E
  have hcard : Nat.card (ResidueField (baseIntegers K)) = Nat.card 𝓀[K] :=
    Nat.card_congr (localResidueEquiv K).toEquiv
  have h := finiteUnramifiedFrobenius_residue K E hE (residue C b)
  rw [residueHom_apply, hcard] at h
  let z : C := integerAut K E s b - b ^ Nat.card 𝓀[K]
  have hz : residue C z = 0 := by
    change residue C (integerAut K E s b - b ^ Nat.card 𝓀[K]) = 0
    rw [RingHom.map_sub, RingHom.map_pow, h, sub_self]
  have hv : spectralValuation K E (z : E) < 1 :=
    (Valuation.mem_maximalIdeal_iff _ (spectralValuation K E)).mp ((residue_eq_zero_iff z).mp hz)
  let v := localDivisionSubfieldValuation K D ι
  have hw : v (z : E) < v 1 := by
    rw [← not_le, ← subfieldSpectralValuation_le_iff K D E ι, map_one]
    exact not_le_of_gt hv
  rw [map_one] at hw
  change localReducedNormValuation K D (ι (s (a : E) - (a : E) ^ Nat.card 𝓀[K])) < 1 at hw
  rw [map_sub] at hw
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (localReducedNormValuation K D _) < 1
  rw [← map_one e]
  exact e.toOrderIso.lt_iff_lt.mpr hw

variable (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
  reciprocalClass (CentralSimple.reducedDegree K D))

/-- The chosen embedding has the actual étale integer subfield in the order. -/
theorem drinfeldUnramifiedEmbedding_finiteEtale :
    IsUnramifiedSubfieldOfReducedDegree K D (drinfeldUnramifiedEmbedding K D hInv) :=
  subfieldArithmeticUnramifiedOfReducedDegree K D (drinfeldUnramifiedField K D)
    (drinfeldUnramifiedEmbedding K D hInv) (drinfeldUnramifiedField_unramified K D)
    (drinfeldUnramifiedField_degree K D)

/-- All three cyclic relations hold for the actual chosen embedded field and
normalized division uniformizer. -/
theorem drinfeldUnramifiedEmbedding_cyclicRelations {π : 𝒪[K]} (hπ : Irreducible π) :
    HasDrinfeldCyclicRelations (drinfeldUnramifiedEmbedding K D hInv) π :=
  ⟨drinfeldArithmeticUniformizer K D hInv hπ,
    finiteUnramifiedFrobenius K (drinfeldUnramifiedField K D) (drinfeldUnramifiedField_unramified K D),
    drinfeldArithmeticUniformizer_pow K D hInv hπ,
    drinfeldArithmeticUniformizer_mul K D hInv hπ,
    subfieldArithmeticFrobenius_sub_lt_one K D (drinfeldUnramifiedField K D)
      (drinfeldUnramifiedEmbedding K D hInv) (drinfeldUnramifiedField_unramified K D)⟩

end Langlands.FormalGroup.LocalDivision
