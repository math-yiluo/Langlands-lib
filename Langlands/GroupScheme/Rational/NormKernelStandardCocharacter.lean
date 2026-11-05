import Langlands.GroupScheme.Rational.NormKernelCocharacter

/-! # Standard cocharacters annihilating ambient rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

variable [Fintype (relativeWeylGroup i)] [IsAffineHom G.X.hom]

/-- The correction multiplies every actual root pairing by the Weyl group order. -/
theorem latticePairing_normKernelCocharacter_root_of_relativeRootSystem
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (ζ : cocharacterLattice T) (α : characterLattice T) (hα : α ∈ relativeRoots i) :
    latticePairing T α (_root_.Langlands.GroupScheme.normKernelCocharacter i ζ) =
      Fintype.card (relativeWeylGroup i) • latticePairing T α ζ := by
  simp only [normKernelCocharacter, map_sub, map_nsmul]
  rw [latticePairing_relativeWeylCocharacterSum_eq_zero i hT
    (fun _ ha => hRoots.exists_isRelativeReflection ha) ζ α hα, sub_zero]

/-- Every standard face has a standard cocharacter annihilating all ambient characters. -/
theorem IsStandardCocharacter.normKernelCocharacter_of_relativeRootSystem
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (ν : cocharacterLattice T) {J : Set (characterLattice T)}
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν J ζ) :
    IsStandardCocharacter i ν J (_root_.Langlands.GroupScheme.normKernelCocharacter i ζ) := by
  refine ⟨hζ.1, ?_, ?_⟩
  · intro α hα
    rw [latticePairing_normKernelCocharacter_root_of_relativeRootSystem i hT hRoots ζ α ((hζ.1 hα).1.1),
      hζ.2.1 α hα, smul_zero]
  · intro α hα hαJ
    rw [latticePairing_normKernelCocharacter_root_of_relativeRootSystem i hT hRoots ζ α hα.1.1]
    have hcard : 0 < (Fintype.card (relativeWeylGroup i) : ℤ) := by
      exact_mod_cast Fintype.card_pos
    simpa only [nsmul_eq_mul] using mul_pos hcard (hζ.2.2 α hα hαJ)

end Langlands.GroupScheme
