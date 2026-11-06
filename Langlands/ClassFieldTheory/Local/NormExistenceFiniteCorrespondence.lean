import Langlands.ClassFieldTheory.Local.NormExistenceNormTransfer
import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof

/-! # Compatible finite norm equivalences and fixed-field norm images -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsGalois L M]

/-- The actual degree-minus-two cup map intertwines subgroup inclusion and norm. -/
theorem abelianizationCupToNormQuotient_corestriction
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers)
    (hcores : FundamentalClassTateCorestriction K L M invKM invLM)
    (c : relativeCohomology K M 2) (d : relativeCohomology L M 2)
    (hc : IsFundamentalClass K M invKM c) (hd : IsFundamentalClass L M invLM d)
    (x : Additive (Abelianization Gal(M/L))) :
    abelianizationCupToNormQuotient K M c (relativeAbelianizationInclusion K L M x) =
      (Langlands.LocalClassField.normQuotientTowerNorm K L M).toAdditive
        (abelianizationCupToNormQuotient L M d x) := by
  obtain ⟨y, rfl⟩ := (integralTateMinusTwoEquiv L M).surjective x
  rw [← integralTateMinusTwoEquiv_corestriction,
    abelianizationCupToNormQuotient_comparison,
    abelianizationCupToNormQuotient_comparison]
  change tateZeroEquivNormQuotient K M
    (relativeTateCup K M (-2) c (integralTateCorestriction K L M (-2) y)) = _
  rw [← hcores c d hc hd (-2) y]
  change tateZeroEquivNormQuotient K M
    (relativeTateCorestriction K L M 0 (relativeTateCup L M (-2) d y)) = _
  rw [tateZeroEquivNormQuotient_corestriction]
  rfl

end Tower

variable {p : ℕ} [Fact p.Prime]

/-- Choose the fundamental class of one invariant family for each finite extension. -/
def normCorrespondenceFundamentalClass (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (F : PadicField.{u} p) (M : Type u)
    [Field M] [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier M] : relativeCohomology F.Carrier M 2 :=
  Classical.choose (hFund F M).1

lemma normCorrespondenceFundamentalClass_spec (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (F : PadicField.{u} p) (M : Type u)
    [Field M] [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier M] :
    IsFundamentalClass F.Carrier M (I.relative F M)
      (normCorrespondenceFundamentalClass I hFund F M) :=
  (Classical.choose_spec (hFund F M).1).1

/-- Cup equivalence for the selected fundamental class of the same family. -/
def normCorrespondenceEquiv (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (F : PadicField.{u} p) (M : Type u)
    [Field M] [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier M] :
    Abelianization Gal(M/F.Carrier) ≃*
      Langlands.LocalClassField.NormQuotient F.Carrier M :=
  abelianizationCupEquiv F.Carrier M (normCorrespondenceFundamentalClass I hFund F M)
    (hTate F M _ (normCorrespondenceFundamentalClass_spec I hFund F M) (-2))

set_option maxRecDepth 2048 in
/-- The selected finite equivalences commute with actual norms in Galois towers. -/
theorem normCorrespondenceEquiv_corestriction (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (hTransfers : I.TateTransferCompatibility)
    (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier M] [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier E.Carrier] [IsGalois F.Carrier M] [IsGalois E.Carrier M]
    (x : Abelianization Gal(M/E.Carrier)) :
    normCorrespondenceEquiv I hFund hTate F M
        (Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier) x) =
      Langlands.LocalClassField.normQuotientTowerNorm F.Carrier E.Carrier M
        (normCorrespondenceEquiv I hFund hTate E M x) := by
  exact congrArg Additive.toMul
    (abelianizationCupToNormQuotient_corestriction F.Carrier E.Carrier M
    (I.relative F M) (I.relative E M) (hTransfers F E M).2 _ _
    (normCorrespondenceFundamentalClass_spec I hFund F M)
    (normCorrespondenceFundamentalClass_spec I hFund E M) (Additive.ofMul x))

end Langlands.ClassFieldTheory.Local
