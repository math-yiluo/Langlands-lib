import Langlands.ClassFieldTheory.Local.TateCup
import Langlands.Cohomology.Tate.LowDegree

/-! # The degree-minus-two local cup map on the Galois abelianization -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- Actual integral Tate degree minus two is the Galois abelianization. -/
def integralTateMinusTwoEquiv :
    integralTateCohomology K L (-2) ≃+ Additive (Abelianization Gal(L/K)) := by
  letI := Fintype.ofFinite Gal(L/K)
  exact Langlands.Tate.integralMinusTwoEquiv Gal(L/K)

/-- The comparison sends the first-homology single-chain class with coefficient
one to the class of the same automorphism in the abelianization. -/
theorem integralTateMinusTwoEquiv_class (σ : Gal(L/K)) :
    letI := Fintype.ofFinite Gal(L/K)
    integralTateMinusTwoEquiv K L
      (Langlands.Tate.minusTwoClass (Langlands.Tate.integralTrivial Gal(L/K))
        σ (1 : IntegerScalars.{u})) =
      Additive.ofMul (Abelianization.of σ) := by
  let := Fintype.ofFinite Gal(L/K)
  exact Langlands.Tate.integralMinusTwoEquiv_class σ

variable [IsGalois K L]

/-- The actual degree-minus-two cup map, with both source and target identified.
This map is defined for any ordinary relative degree-two class. -/
def abelianizationCupToNormQuotient (c : relativeCohomology K L 2) :
    Additive (Abelianization Gal(L/K)) →+
      Additive (Langlands.LocalClassField.NormQuotient K L) :=
  (negativeTwoCupToNormQuotient K L c).comp
    (integralTateMinusTwoEquiv K L).symm.toAddMonoidHom

/-- The new presentation commutes with the actual Tate source comparison. -/
theorem abelianizationCupToNormQuotient_comparison
    (c : relativeCohomology K L 2) (x : integralTateCohomology K L (-2)) :
    abelianizationCupToNormQuotient K L c (integralTateMinusTwoEquiv K L x) =
      negativeTwoCupToNormQuotient K L c x := by
  exact congrArg (negativeTwoCupToNormQuotient K L c)
    ((integralTateMinusTwoEquiv K L).symm_apply_apply x)

/-- Source and target identifications preserve and reflect cup bijectivity. -/
theorem abelianizationCupToNormQuotient_bijective_iff
    (c : relativeCohomology K L 2) :
    Function.Bijective (abelianizationCupToNormQuotient K L c) ↔
      Function.Bijective (relativeTateCup K L (-2) c) := by
  constructor
  · intro h
    apply (negativeTwoCupToNormQuotient_bijective_iff K L c).mp
    have h' := h.comp (integralTateMinusTwoEquiv K L).bijective
    simpa only [Function.comp_def, abelianizationCupToNormQuotient_comparison] using h'
  · intro h
    exact ((negativeTwoCupToNormQuotient_bijective_iff K L c).mpr h).comp
      (integralTateMinusTwoEquiv K L).symm.bijective

/-- The multiplicative cup equivalence is constructed only after its
degree-minus-two bijectivity has been proved. -/
def abelianizationCupEquiv (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c)) :
    Abelianization Gal(L/K) ≃* Langlands.LocalClassField.NormQuotient K L :=
  MulEquiv.toAdditive.symm
    (AddEquiv.ofBijective (abelianizationCupToNormQuotient K L c)
      ((abelianizationCupToNormQuotient_bijective_iff K L c).mpr h))

/-- Bundling cup bijectivity leaves the constructed forward map unchanged. -/
theorem abelianizationCupEquiv_apply (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c))
    (σ : Abelianization Gal(L/K)) :
    Additive.ofMul (abelianizationCupEquiv K L c h σ) =
      abelianizationCupToNormQuotient K L c (Additive.ofMul σ) := rfl

/-- Conditional inverse of the cup equivalence. For the positive fundamental
class convention, this is the arithmetic reciprocity construction. -/
def arithmeticReciprocityOfCup (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c)) :
    Langlands.LocalClassField.NormQuotient K L ≃* Abelianization Gal(L/K) :=
  (abelianizationCupEquiv K L c h).symm

/-- The arithmetic construction is inverse to the actual cup map. -/
theorem cup_arithmeticReciprocityOfCup (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c))
    (a : Langlands.LocalClassField.NormQuotient K L) :
    abelianizationCupToNormQuotient K L c
      (Additive.ofMul (arithmeticReciprocityOfCup K L c h a)) = Additive.ofMul a := by
  rw [← abelianizationCupEquiv_apply K L c h]
  unfold arithmeticReciprocityOfCup
  rw [MulEquiv.apply_symm_apply]

/-- The geometric convention inverts the output of the arithmetic construction
in the actual abelianized Galois group. -/
def geometricReciprocityOfCup (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c)) :
    Langlands.LocalClassField.NormQuotient K L ≃* Abelianization Gal(L/K) :=
  (arithmeticReciprocityOfCup K L c h).trans (MulEquiv.inv _)

/-- The convention change is output inversion, in addition to the inverse
equivalence used to define arithmetic reciprocity. -/
theorem geometricReciprocityOfCup_eq_inv (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c))
    (a : Langlands.LocalClassField.NormQuotient K L) :
    geometricReciprocityOfCup K L c h a =
      (arithmeticReciprocityOfCup K L c h a)⁻¹ := rfl

end Langlands.ClassFieldTheory.Local
