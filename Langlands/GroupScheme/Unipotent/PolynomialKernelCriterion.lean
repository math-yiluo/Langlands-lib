import Langlands.GroupScheme.Unipotent.PolynomialKernelAffineLine

/-! # Affine-line constancy and central additive subgroups of polynomial kernels -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

/-- Failure of actual affine-line constancy produces a closed standard additive
subgroup of the actual polynomial kernel, with a homomorphic retraction. -/
theorem exists_closed_kernel_section_of_not_hasConstantAffineLineMaps
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hG : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    ∃ s : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf),
      IsClosedSubgroup s ∧
        ∃ r : kernel (polynomialRow f hf) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
          s ≫ r = 𝟙 _ := by
  obtain ⟨φ, hφ, hrel⟩ :=
    hasNonconstantPolynomialKernelCurve_of_not_hasConstantAffineLineMaps f hf hG
  exact exists_closed_kernel_section_of_nonconstant f hf φ hφ hrel

/-- A chosen actual closed additive section when the polynomial kernel admits a
nonconstant affine-line map. Its properties are stated separately below. -/
def polynomialKernelSectionOfNotConstant
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hG : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ kernel (polynomialRow f hf) :=
  Classical.choose (exists_closed_kernel_section_of_not_hasConstantAffineLineMaps f hf hG)

theorem polynomialKernelSectionOfNotConstant_spec
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hG : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    IsClosedSubgroup (polynomialKernelSectionOfNotConstant f hf hG) ∧
      ∃ r : kernel (polynomialRow f hf) ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
        polynomialKernelSectionOfNotConstant f hf hG ≫ r = 𝟙 _ :=
  Classical.choose_spec
    (exists_closed_kernel_section_of_not_hasConstantAffineLineMaps f hf hG)

/-- Actual affine-line constancy is equivalent to the absence of nonconstant
polynomial curves in the separated-variable kernel equation. -/
theorem hasConstantAffineLineMaps_polynomialKernel_iff
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasConstantAffineLineMaps (kernel (polynomialRow f hf)) ↔
      ¬ HasNonconstantPolynomialKernelCurve f := by
  constructor
  · intro hG h
    obtain ⟨φ, hφ, hrel⟩ := h
    obtain ⟨s, hs, _⟩ := exists_closed_kernel_section_of_nonconstant f hf φ hφ hrel
    exact hG.not_isVectorGroupOfDimension_one_closed_subgroup s hs
      ⟨VectorGroup.coordinates (CommRingCat.of k) 1,
        VectorGroup.isNaturalVectorCoordinates⟩
  · intro h
    by_contra hG
    exact h (hasNonconstantPolynomialKernelCurve_of_not_hasConstantAffineLineMaps f hf hG)

/-- The central additive-subgroup criterion holds for every actual additive
polynomial kernel, without geometric regularity assumptions. -/
theorem hasConstantAffineLineMaps_polynomialKernel_iff_not_exists_central_additive
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasConstantAffineLineMaps (kernel (polynomialRow f hf)) ↔
      ¬ ∃ (V : GroupScheme (Spec (CommRingCat.of k)))
        (j : V ⟶ kernel (polynomialRow f hf)),
          IsClosedSubgroup j ∧ IsCentral j ∧ IsVectorGroupOfDimension V 1 := by
  have : IsCommMonObj (VectorGroup.groupScheme (CommRingCat.of k) n).X := by
    apply (isCommMonObj_iff_isMulCommutative _).mpr
    intro T
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (VectorGroup.coordinates (CommRingCat.of k) n T).injective
    simp only [map_mul, mul_comm]
  constructor
  · exact HasConstantAffineLineMaps.not_exists_central_additive_closed_subgroup
  · intro h
    by_contra hG
    let s := polynomialKernelSectionOfNotConstant f hf hG
    obtain ⟨hs, _⟩ := polynomialKernelSectionOfNotConstant_spec f hf hG
    apply h
    refine ⟨VectorGroup.groupScheme (CommRingCat.of k) 1, s, hs, ?_,
      ⟨VectorGroup.coordinates (CommRingCat.of k) 1,
        VectorGroup.isNaturalVectorCoordinates⟩⟩
    intro T x T' b y
    exact Commute.all (b ≫ (x ≫ s.hom.hom)) y

/-- Constancy of actual affine-line maps into additive polynomial kernels is
invariant under every algebraic Galois extension, with independent field universes. -/
theorem hasConstantAffineLineMaps_polynomialKernel_iff_of_isGalois
    {K : Type v} [Field K] [Algebra k K] [IsGalois k K]
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasConstantAffineLineMaps
        (kernel (polynomialRow (fun i => (f i).map (algebraMap k K))
          (fun i => (hf i).map_algebraMap))) ↔
      HasConstantAffineLineMaps (kernel (polynomialRow f hf)) := by
  rw [hasConstantAffineLineMaps_polynomialKernel_iff,
    hasConstantAffineLineMaps_polynomialKernel_iff,
    hasNonconstantPolynomialKernelCurve_iff_of_isGalois f hf]

end Langlands.GroupScheme.Unipotent
