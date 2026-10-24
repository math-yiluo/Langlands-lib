import Langlands.Representation.Classification.RegularLanglandsStatement
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Twist.LeviRealPower

/-! Algebraic comparison of the two actual standard-module presentations. -/

noncomputable section

namespace Langlands.RegularHeadExistence

universe uF uV

/-- The tensor of the individual real determinant twists is the real Levi
twist of the untwisted tensor, on the same tensor carrier. -/
theorem blockTensor_twistedBlocks
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (t : Fin B.length → ℝ) :
    letI := T.topology
    B.blockTensor (fun i => (T.twistedBlocks B A t i).representation) =
      T.leviRealPowerTwist B t (B.blockTensor (fun i => (A i).representation)) := by
  let := T.topology
  let χ : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨T.leviRealPowerCharacter B t, T.isOpen_ker_leviRealPowerCharacter B t⟩
  have hc (i : Fin B.length) :
      (χ.coordinate i).toMonoidHom = T.determinantPowerCharacter (B.size i) (t i) := by
    apply MonoidHom.ext
    intro g
    change T.leviRealPowerCharacter B t (Pi.mulSingle i g) = _
    rw [T.leviRealPowerCharacter_apply]
    rw [Finset.prod_eq_single i]
    · simp only [Pi.mulSingle_eq_same]
    · intro j _ hji
      rw [Pi.mulSingle_eq_of_ne hji, map_one]
    · simp
  convert χ.external_coordinate_twist (fun i => (A i).representation) using 1
  simp only [hc, PadicField.TopologicalData.twistedBlocks,
    PadicField.TopologicalData.segmentFactor, SmoothRep.twist_representation,
    PadicField.TopologicalData.leviRealPowerTwist, χ,
    GeneralLinear.BlockShape.blockTensor]
  rfl

section StandardModule

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (d : T.TemperedLanglandsDatum.{uV, uF} n)

/-- Actual normalized-induction equivalence between the standard module and
induction of the real twist of its untwisted product-Levi tensor. -/
def standardModuleLeviTwistEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    d.standardModule.representation.Equiv
      (T.normalizedParabolicInduced d.shape
        (T.leviRealPowerTwist d.shape d.exponent
          (d.shape.blockTensor (fun i => (d.blocks i).representation)))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact T.normalizedParabolicInducedEquiv d.shape
    (equivOfRepresentationEq (blockTensor_twistedBlocks T d.shape d.blocks d.exponent))

/-- A head of the Levi-twist induction gives the actual smooth canonical head
of the standard module, preserving equality of all irreducible-quotient kernels. -/
theorem standardModule_hasHead_of_leviTwistHead
    (h : letI := T.topology
      Classification.HasIrreducibleHead
        (T.normalizedParabolicInduced d.shape
          (T.leviRealPowerTwist d.shape d.exponent
            (d.shape.blockTensor (fun i => (d.blocks i).representation))))) :
    letI := T.topology
    d.IsLanglandsHead d.standardModule.headQuotient := by
  let := T.topology
  obtain ⟨W, hW, hModule, π, hπ⟩ := h
  exact SmoothRep.isIrreducibleHead_headQuotient_iff.mpr
    ⟨W, hW, hModule, π, hπ.of_equiv (standardModuleLeviTwistEquiv T d).symm⟩


end StandardModule

end Langlands.RegularHeadExistence
