import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.Algebra.BrauerComparison.BaseChangeChart
import Langlands.Algebra.BrauerComparison.RelativeLaws
import Langlands.LocalField.Normalization.Proof

/-! # Comparison of the p-adic class-field and Brauer invariant normalizations -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open Langlands.LocalGalois Langlands.LocalGalois.Separable
open ValuativeRel IsLocalRing

universe u v

variable {p : ℕ} [Fact p.Prime] (P : PadicField.{u} p)

section PadicNorm

local instance : NontriviallyNormedField P.Carrier := P.canonicalNormedField
local instance : IsUltrametricDist P.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := P.Carrier))
local instance : CompleteSpace P.Carrier := P.canonical_complete_proper.1

private abbrev padicBaseIntegers := baseIntegers P.Carrier

variable (L : Type u) [Field L] [Algebra P.Carrier L] [FiniteDimensional P.Carrier L]

private abbrev padicExtensionIntegers := extensionIntegers P.Carrier L

private theorem padicExtensionIntegers_iff (x : L) :
    IsIntegral (padicBaseIntegers P) x ↔ x ∈ padicExtensionIntegers P L :=
  integral_iff_mem_spectralIntegers P.Carrier L x

private abbrev padicResidueHom := residueHom P.Carrier L

end PadicNorm

local instance : TopologicalSpace P.Carrier := P.canonicalTopologicalData.topology
local instance : ValuativeRel P.Carrier := P.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField P.Carrier := P.canonicalTopologicalData.localField
local instance : NontriviallyNormedField P.Carrier := localNormedField P.Carrier
local instance : IsUltrametricDist P.Carrier := localNormedField_ultrametric P.Carrier
local instance : CompleteSpace P.Carrier := localNormedField_complete P.Carrier
local instance : Finite (ResidueField (baseIntegers P.Carrier)) := localResidue_finite P.Carrier

private theorem baseIntegers_eq_padicBaseIntegers :
    baseIntegers P.Carrier = padicBaseIntegers P := by
  ext x
  change x ∈ (NormedField.valuation (K := P.Carrier)).integer ↔ P.canonicalValuation x ≤ 1
  rw [localNormedField_integer]
  change valuation P.Carrier x ≤ 1 ↔ P.canonicalValuation x ≤ 1
  let : P.canonicalValuation.Compatible := Valuation.Compatible.ofValuation _
  rw [← (valuation P.Carrier).vle_one_iff, ← P.canonicalValuation.vle_one_iff]

section Residue

variable (L : Type u) [Field L] [Algebra P.Carrier L] [FiniteDimensional P.Carrier L]

private theorem extensionIntegers_eq_padicExtensionIntegers :
    extensionIntegers P.Carrier L = padicExtensionIntegers P L := by
  ext x
  rw [← integral_iff_mem_spectralIntegers, ← padicExtensionIntegers_iff]
  exact Iff.of_eq (congrArg (fun R : ValuationSubring P.Carrier => IsIntegral R x)
    (baseIntegers_eq_padicBaseIntegers P))

private def padicResidueEquiv :
    ResidueField (extensionIntegers P.Carrier L) ≃+*
      ResidueField (padicExtensionIntegers P L) :=
  ResidueField.mapEquiv (RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (extensionIntegers_eq_padicExtensionIntegers P L)))

private theorem padicResidueEquiv_residueHom (σ : L ≃ₐ[P.Carrier] L)
    (x : ResidueField (extensionIntegers P.Carrier L)) :
    padicResidueEquiv P L (residueHom P.Carrier L σ x) =
      padicResidueHom P L σ (padicResidueEquiv P L x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp only [padicResidueEquiv, residueHom_apply,
    ResidueField.mapEquiv_apply, ResidueField.map_residue]
  congr 1

end Residue

private theorem card_padicBaseResidue :
    Nat.card (ResidueField (baseIntegers P.Carrier)) =
      Nat.card (ResidueField (padicBaseIntegers P)) := by
  let e : baseIntegers P.Carrier ≃+* padicBaseIntegers P :=
    RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (baseIntegers_eq_padicBaseIntegers P))
  exact Nat.card_congr (ResidueField.mapEquiv e).toEquiv

set_option maxHeartbeats 600000 in
/-- The arithmetic coordinate on the spectral unramified stage has the same
normalization for the p-adic field bundle. -/
theorem isArithmeticUnramifiedCoordinate_finiteUnramified
    (E : IntermediateField P.Carrier (SeparableClosure P.Carrier))
    [FiniteDimensional P.Carrier E] [IsGalois P.Carrier E]
    [NeZero (Module.finrank P.Carrier E)] (hE : ArithmeticUnramified P.Carrier E) :
    IsArithmeticUnramifiedCoordinate P E (finiteUnramifiedCyclicCoordinate P.Carrier E hE) := by
  change Function.Injective (padicResidueHom P E) ∧
    ∀ x, padicResidueHom P E
      (cyclicCoordinateGenerator (finiteUnramifiedCyclicCoordinate P.Carrier E hE)) x =
      x ^ Nat.card (ResidueField (padicBaseIntegers P))
  constructor
  · intro σ τ hστ
    apply finiteUnramified_residueHom_injective P.Carrier E hE
    apply AlgEquiv.ext
    intro x
    apply (padicResidueEquiv P E).injective
    rw [padicResidueEquiv_residueHom P E σ x, padicResidueEquiv_residueHom P E τ x, hστ]
  · intro x
    obtain ⟨y, rfl⟩ := (padicResidueEquiv P E).surjective x
    rw [← padicResidueEquiv_residueHom P E _ y, cyclicCoordinateGenerator_finiteUnramified,
      finiteUnramifiedFrobenius_residue P.Carrier E hE y, map_pow]
    exact congrArg (fun n : ℕ => padicResidueEquiv P E y ^ n) (card_padicBaseResidue P)

set_option maxHeartbeats 600000 in
/-- On an unramified stage, arithmetic normalization determines the invariant
from the cyclic class of a uniformizer. -/
theorem relativeInvariant_eq_spectralUnramifiedInvariant
    (I : InvariantFamily.{u, u} p) (hI : I.ArithmeticNormalization)
    (E : IntermediateField P.Carrier (SeparableClosure P.Carrier))
    [FiniteDimensional P.Carrier E] [IsGalois P.Carrier E]
    (hE : ArithmeticUnramified P.Carrier E) (x : relativeCohomology P.Carrier E 2) :
    I.relative P E x = spectralUnramifiedInvariant P.Carrier E hE x := by
  let d := Module.finrank P.Carrier E
  have hd : 0 < d := Module.finrank_pos
  let : NeZero d := ⟨hd.ne'⟩
  let χ := finiteUnramifiedCyclicCoordinate P.Carrier E hE
  let T := P.canonicalTopologicalData
  have hπ₀ : T.uniformizer ≠ 0 := by
    intro h
    have hord := T.ord_uniformizer
    rw [h, T.ord_zero] at hord
    omega
  let π : P.Carrierˣ := Units.mk0 T.uniformizer hπ₀
  let c := cyclicClass P.Carrier E χ.toMonoidHom π
  have hc : spectralUnramifiedInvariant P.Carrier E hE c = reciprocalClass d := by
    change spectralUnramifiedInvariant P.Carrier E hE
      (cyclicClass P.Carrier E (finiteUnramifiedCyclicCoordinate P.Carrier E hE).toMonoidHom π) = _
    rw [spectralUnramifiedInvariant_cyclicClass]
    change rationalClass ((T.ord T.uniformizer : ℚ) / d) = _
    simp only [T.ord_uniformizer, Int.cast_one, reciprocalClass, one_div]
  have hIc : I.relative P E c = reciprocalClass d :=
    hI P E d χ (isArithmeticUnramifiedCoordinate_finiteUnramified P E hE) π T.ord_uniformizer
  have hx : spectralUnramifiedInvariant P.Carrier E hE x ∈ denominatorSubgroup d := by
    rw [← spectralUnramifiedInvariant_range P.Carrier E hE]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := (denominatorEquiv d hd).surjective ⟨_, hx⟩
  have hgen : x = z.val • c := by
    apply spectralUnramifiedInvariant_injective P.Carrier E hE
    rw [map_nsmul, hc]
    have hz' : z.val • (1 : ZMod d) = z := by simp [nsmul_eq_mul]
    calc
      _ = (denominatorEquiv d hd z : RationalModIntegers) := congrArg Subtype.val hz.symm
      _ = (denominatorEquiv d hd (z.val • (1 : ZMod d)) : RationalModIntegers) := by rw [hz']
      _ = _ := by rw [map_nsmul, AddSubgroup.coe_nsmul, denominatorEquiv_one]
  rw [hgen, map_nsmul, map_nsmul, hIc, hc]

section Brauer

open Langlands.Brauer Langlands.BrauerComparison
open scoped TensorProduct

/-- On every finite Galois splitting chart the relative class-field invariant
agrees with the intrinsic local Brauer invariant. -/
def RelativeInvariantBrauerComparisonStatement : Prop :=
  ∀ (I : InvariantFamily.{u, u} p), I.ArithmeticNormalization → I.InflationCompatibility →
    ∀ (L : Type u) [Field L] [Algebra P.Carrier L]
      [FiniteDimensional P.Carrier L] [IsGalois P.Carrier L]
      (A : CSA.{u, u} P.Carrier) {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
      (e : L ⊗[P.Carrier] A ≃ₐ[L] Matrix J J L),
      I.relative P L (relativeClass e) = localBrauerInvariant P.Carrier (classOf A)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 150000 in
theorem relativeInvariant_eq_localBrauerInvariant : RelativeInvariantBrauerComparisonStatement.{u, v} P := by
  intro I hI hInf L _ _ _ _ A J _ _ _ e
  obtain ⟨S, d, hd, ⟨f⟩⟩ := exists_unramifiedSplittingChart P.Carrier A
  let E := S.field
  let : FiniteDimensional P.Carrier E := S.finiteDimensional
  let : IsGalois P.Carrier E := S.isGalois
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let j : L →ₐ[P.Carrier] SeparableClosure P.Carrier := IsSepClosed.lift
  let : FiniteDimensional P.Carrier j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
  let : IsGalois P.Carrier j.fieldRange := IsGalois.of_algEquiv j.equivFieldRange
  let N := j.fieldRange ⊔ E
  let : IsGalois P.Carrier N := ⟨⟩
  let jL := (IntermediateField.inclusion (show j.fieldRange ≤ N from le_sup_left)).comp
    j.equivFieldRange.toAlgHom
  let jE := IntermediateField.inclusion (show E ≤ N from le_sup_right)
  let : Algebra L N := jL.toRingHom.toAlgebra
  let : IsScalarTower P.Carrier L N := IsScalarTower.of_algHom jL
  let : Algebra E N := jE.toRingHom.toAlgebra
  let : IsScalarTower P.Carrier E N := IsScalarTower.of_algHom jE
  let : FiniteDimensional L N := FiniteDimensional.right P.Carrier L N
  let : FiniteDimensional E N := FiniteDimensional.right P.Carrier E N
  calc
    _ = I.relative P N (relativeClass (enlargedSplittingChart N e)) := by
      rw [relativeClass_enlargedSplittingChart]
      exact (hInf P L N (relativeClass e)).symm
    _ = I.relative P N (relativeClass (enlargedSplittingChart N f)) :=
      congrArg (I.relative P N) (relativeClass_eq_of_indices _ _)
    _ = I.relative P E (relativeClass f) := by
      rw [relativeClass_enlargedSplittingChart]
      exact hInf P E N (relativeClass f)
    _ = spectralUnramifiedInvariant P.Carrier E S.unramified (relativeClass f) :=
      relativeInvariant_eq_spectralUnramifiedInvariant P I hI E S.unramified _
    _ = _ := (localBrauerInvariant_at_chart P.Carrier A E S.unramified f).symm

end Brauer

end Langlands.ClassFieldTheory.Local
