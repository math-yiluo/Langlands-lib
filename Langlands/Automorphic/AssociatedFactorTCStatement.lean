import Langlands.Automorphic.AssociatedFactorStatement

/-! # Totally complex forms of Henniart's local factors of weakly associated pairs

`AssociatedGammaStatement`, `AssociatedTemperedFactorStatement`,
`AssociatedSupercuspidalInductionStatement` and `AssociatedCuspidalFactorStatement`
(Henniart 2000, Théorème 2.3, Corollaire 2.3, Théorème 2.4 and Corollaire 2.4), each with the
instance argument `[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the
same universe levels, the rest verbatim. Proposition definitions only. See the paired Markdown
for the reason and the sources.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Global

open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u uV uP uQ uE

namespace RelativeWeilGroup

/-- The totally complex form of `AssociatedGammaStatement` (Henniart 2000, Théorème 2.3):
the same statement for a totally complex base field `F`; the rest is verbatim. -/
def AssociatedGammaTCStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ {r t : ℕ} (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    IsWeaklyAssociatedClass.{u, uV, uP} S' T'.isoClass →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap v w.1 e ι →
  ∀ ψv : Correspondence.NontrivialAdditiveCharacter (padicField v),
    IsCanonicalFiniteAdditiveComponent ψ v ψv →
  ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε),
    IsPairGammaMatch.{u, uV, uE} (padicField v) eC ε hε ψv
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
      (localPairClass S ι) (localPairClass S' ι)

/-- The totally complex form of `AssociatedTemperedFactorStatement` (Henniart 2000,
Corollaire 2.3): the same statement for a totally complex base field `F`; the rest is
verbatim. -/
def AssociatedTemperedFactorTCStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ {r t : ℕ} (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    IsWeaklyAssociatedClass.{u, uV, uP} S' T'.isoClass →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible),
    (letI := (padicField v).canonicalTopologicalData.topology;
      PadicField.TopologicalData.IsTempered (padicField v).canonicalTopologicalData
        ((P.localComponent v).padicObject hI hA).obj.representation) →
    (letI := (padicField v).canonicalTopologicalData.topology;
      PadicField.TopologicalData.IsTempered (padicField v).canonicalTopologicalData
        ((P'.localComponent v).padicObject hI' hA').obj.representation) →
  ∀ (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap v w.1 e ι →
    (localComponent S ι).IsUnitary → (localComponent S' ι).IsUnitary →
  ∀ ψv : Correspondence.NontrivialAdditiveCharacter (padicField v),
    IsCanonicalFiniteAdditiveComponent ψ v ψv →
    IsPairFactorMatch.{u, uV, uE} (padicField v) ψv
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
      (localPairClass S ι) (localPairClass S' ι)
      (localPairClass S.dual ι) (localPairClass S'.dual ι)

/-- The totally complex form of `AssociatedSupercuspidalInductionStatement` (Henniart 2000,
Théorème 2.4): the same statement for a totally complex base field `F`; the rest is
verbatim. -/
def AssociatedSupercuspidalInductionTCStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r),
    S.IsIrreducible → S.IsUnitary → HasUnitaryCentralCharacter T →
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T) (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible),
    letI := (padicField v).canonicalTopologicalData.topology
    ∃ (B : GeneralLinear.BlockShape (r + 1))
      (σ : ∀ i, GeneralLinear.SupercuspidalRep.{u, u}
        (F := (padicField v).Carrier) (n := B.size i)),
      (∀ i, IsUnitarizable (σ i).obj.representation) ∧
        Nonempty (((P.localComponent v).padicObject hI hA).obj.representation.Equiv
          ((padicField v).canonicalTopologicalData.normalizedProductInduced B
            fun i => (σ i).obj.representation))

/-- The totally complex form of `AssociatedCuspidalFactorStatement` (Henniart 2000,
Corollaire 2.4): the same statement for a totally complex base field `F`; the rest is
verbatim. -/
def AssociatedCuspidalFactorTCStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ {r t : ℕ} (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    S.IsIrreducible → S.IsUnitary → S'.IsIrreducible → S'.IsUnitary →
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    IsWeaklyAssociatedClass.{u, uV, uP} S' T'.isoClass →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap v w.1 e ι →
  ∀ ψv : Correspondence.NontrivialAdditiveCharacter (padicField v),
    IsCanonicalFiniteAdditiveComponent ψ v ψv →
    IsPairFactorMatch.{u, uV, uE} (padicField v) ψv
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
      (localPairClass S ι) (localPairClass S' ι)
      (localPairClass S.dual ι) (localPairClass S'.dual ι)

end RelativeWeilGroup

end Langlands.ClassFieldTheory.Global
