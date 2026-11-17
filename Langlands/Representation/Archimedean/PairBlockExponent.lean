import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Langlands.LocalFactor.ArchimedeanPairFactor

/-!
# Exponents of the blocks of archimedean pair presentations

The blocks of the pair presentations `realPairBlocks xs ys` and `complexPairBlocks xs ys` of
module `Langlands.LocalFactor.ArchimedeanPairFactor` are built from one block of `xs` and one
block of `ys`, and their exponents add. This module records these facts: the exponents of
`RealCharacterData.mul`, `ComplexCharacterData.mul`, `ComplexCharacterData.conj` and
`ComplexCharacterData.twistReal`, membership in the pair presentations, and the real exponent
`realBlockExponent` of a block of a real pair presentation. See the paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.LocalFactor.Archimedean

/-- The product of two real characters has the sum of the exponents. -/
@[simp]
theorem RealCharacterData.exponent_mul (c d : RealCharacterData) :
    (c.mul d).exponent = c.exponent + d.exponent :=
  rfl

/-- The product of two complex characters has the sum of the exponents. -/
@[simp]
theorem ComplexCharacterData.exponent_mul (c d : ComplexCharacterData) :
    (c.mul d).exponent = c.exponent + d.exponent :=
  rfl

/-- The conjugate of a complex character has the same exponent. -/
@[simp]
theorem ComplexCharacterData.exponent_conj (d : ComplexCharacterData) :
    d.conj.exponent = d.exponent :=
  rfl

/-- The twist of a complex character by a real character composed with the norm has the sum
of the exponents. -/
@[simp]
theorem ComplexCharacterData.exponent_twistReal (d : ComplexCharacterData)
    (c : RealCharacterData) : (d.twistReal c).exponent = d.exponent + c.exponent :=
  rfl

/-- The blocks of the real pair presentation are the blocks of the tensor products of a block
of the first presentation with a block of the second. -/
theorem mem_realPairBlocks {xs ys : List RealBlock} {z : RealBlock} :
    z ∈ realPairBlocks xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, z ∈ x.tensor y := by
  simp only [realPairBlocks, List.mem_flatMap]

/-- The characters of the complex pair presentation are the products of a character of the
first presentation with a character of the second. -/
theorem mem_complexPairBlocks {xs ys : List ComplexCharacterData} {z : ComplexCharacterData} :
    z ∈ complexPairBlocks xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, z = x.mul y := by
  simp only [complexPairBlocks, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end Langlands.LocalFactor.Archimedean

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- Every block of the tensor product of two real blocks has, as real exponent, the sum of the
real exponents of the two blocks. -/
theorem realBlockExponent_of_mem_tensor {x y z : RealBlock} (hz : z ∈ x.tensor y) :
    realBlockExponent z = realBlockExponent x + realBlockExponent y := by
  cases x with
  | character c =>
    cases y with
    | character d =>
      obtain rfl : z = .character (c.mul d) := by simpa [RealBlock.tensor] using hz
      simp [realBlockExponent]
    | induced d =>
      obtain rfl : z = .induced (d.twistReal c) := by simpa [RealBlock.tensor] using hz
      simp only [realBlockExponent, ComplexCharacterData.exponent_twistReal, Complex.add_re]
      exact add_comm _ _
  | induced d =>
    cases y with
    | character c =>
      obtain rfl : z = .induced (d.twistReal c) := by simpa [RealBlock.tensor] using hz
      simp [realBlockExponent]
    | induced e =>
      have h : z = .induced (d.mul e) ∨ z = .induced (d.mul e.conj) := by
        simpa [RealBlock.tensor] using hz
      rcases h with rfl | rfl <;> simp [realBlockExponent]

/-- Every block of the real pair presentation of `xs` and `ys` has, as real exponent, the sum
of the real exponents of a block of `xs` and a block of `ys`. -/
theorem exists_realBlockExponent_of_mem_realPairBlocks {xs ys : List RealBlock} {z : RealBlock}
    (hz : z ∈ realPairBlocks xs ys) :
    ∃ x ∈ xs, ∃ y ∈ ys, realBlockExponent z = realBlockExponent x + realBlockExponent y := by
  obtain ⟨x, hx, y, hy, hzxy⟩ := mem_realPairBlocks.mp hz
  exact ⟨x, hx, y, hy, realBlockExponent_of_mem_tensor hzxy⟩

end Langlands.Archimedean
