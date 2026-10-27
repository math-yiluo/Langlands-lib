import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Langlands.Automorphic.PadicLocalCategory
import Langlands.ClassField.Global.FundamentalClassStatement
import Langlands.Correspondence.FullLFactorCompatibility
import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Correspondence.FullGammaCompatibility
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Unitary.Basic

/-! # Local factors of weakly associated pairs

Henniart (2000), Théorème 2.3, Corollaire 2.3, Théorème 2.4 and Corollaire 2.4, for
representations of the relative Weil group `W_{E/F}` of an arithmetic fundamental class
and actual cuspidal classes of `GL_n` over a number field. Proposition definitions only.
-/

noncomputable section

namespace Langlands.ClassField.Global

open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u uV uP uQ uE

namespace RelativeWeilGroup

section Local

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- `γ(s, π × π', ψ) = γ(s, X ⊗ Y, ψ)` for the supplied local-constant system: a
self-dual measure for `ψ` exists, and for every such measure some `G` is both the
representation-side and the arithmetic pair gamma factor. -/
def IsPairGammaMatch (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} K) : Prop :=
  (∃ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν) ∧
    ∀ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν →
      ∃ G : RatFunc ℂ,
        Correspondence.IsAutomorphicPairGammaFactor K ψ ν π π' G ∧
          Correspondence.IsArithmeticPairGammaFactor K eC ε hε ψ X Y G

/-- `L(s, π × π') = L(s, X ⊗ Y)`: a self-dual measure for `ψ` exists, and for every such
measure some `P` is the representation-side L-polynomial with `1 / P(q^(-s))` the
arithmetic L-factor. -/
def IsPairLMatch (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} K) : Prop :=
  (∃ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν) ∧
    ∀ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν →
      ∃ P : Polynomial ℂ,
        Correspondence.IsAutomorphicPairLPolynomial K ψ ν π π' P ∧
          Correspondence.arithmeticPairLFactor K X Y = (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹

/-- `ε(s, π × π', ψ) = ε(s, X ⊗ Y, ψ)` for the supplied local-constant system: a self-dual
measure for `ψ` exists, and for every such measure some `c q^(-ms)` is both the
representation-side and the arithmetic pair epsilon factor. -/
def IsPairEpsilonMatch (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} K) : Prop :=
  (∃ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν) ∧
    ∀ ν : Correspondence.LocalAdditiveHaarMeasure K, Correspondence.IsSelfDualMeasure K ψ ν →
      ∃ e : ℂˣ × ℤ,
        Correspondence.IsAutomorphicPairEpsilonFactor K ψ ν π π' e ∧
          Correspondence.IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y e.1 e.2

/-- Henniart's three equalities of Corollaire 2.3 at one place: `L(π × π') = L(X ⊗ Y)`,
`L(π^∨ × π'^∨) = L(X^∨ ⊗ Y^∨)` for all contragredient classes, and
`ε(π × π', ψ) = ε(X ⊗ Y, ψ)` for every local-constant system. -/
def IsPairFactorMatch (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
    (X Y Xd Yd : Correspondence.LocalPairClass.{u, uV} K) : Prop :=
  IsPairLMatch.{u, uV} K ψ π π' X Y ∧
    (∀ (πd : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
      (πd' : Correspondence.AutomorphicClass.{u, u} K t.succPNat),
      Correspondence.IsSmoothDual K π πd → Correspondence.IsSmoothDual K π' πd' →
        IsPairLMatch.{u, uV} K ψ πd πd' Xd Yd) ∧
    ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
      (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
      (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε),
      IsPairEpsilonMatch.{u, uV, uE} K eC ε hε ψ π π' X Y

end Local

/-- The class family is the arithmetic fundamental class family for some family of local
invariants forming class formations with the arithmetic normalization: the conclusion
predicates of `GlobalFundamentalClassStatement` hold. -/
def IsArithmeticClassFamily (c : FundamentalClass.ClassFamily.{u}) : Prop :=
  ∃ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) ∧
    FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
      FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c

/-- `ψv` is the component at the finite place `v` of the global additive character `ψ`,
as a character of the p-adic field `F_v` with its canonical topology: `ψv x` is `ψ` of the
adele with `x` at `v` and `0` elsewhere. -/
def IsCanonicalFiniteAdditiveComponent {F : Type u} [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (padicField v)) : Prop := by
  classical
  exact ∀ x : FiniteCompletion F v,
    ψv x = ψ (((0 : InfiniteAdeles F),
      (RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v x :
        FiniteAdeles F)) : Adeles F)

/-- The central character of the actual cuspidal realization is unitary. -/
def HasUnitaryCentralCharacter {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r) :
    Prop :=
  ∃ χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ, (∀ x, ‖(χ x : ℂ)‖ = 1) ∧ T.HasCentralCharacter χ

/-- Henniart (2000), Théorème 2.3 (Henniart 1986, Theorem 4.1), for cuspidal classes:
if `S`, `S'` are weakly associated with the cuspidal classes of `T`, `T'`, then at every
finite place `v`, for every irreducible admissible local component `Π_v`, `Π'_v` of every
spectral presentation, every local map `ι : W_{F_v} → W_{E/F}`, the component `ψ_v` of `ψ`
and every local-constant system, `γ(s, Π_v × Π'_v, ψ_v) = γ(s, S_v ⊗ S'_v, ψ_v)` with
`S_v = S ∘ ι`, `S'_v = S' ∘ ι`. -/
def AssociatedGammaStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)]
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

/-- Henniart (2000), Corollaire 2.3 (Henniart 1986, Proposition 4.5), for cuspidal classes:
in the situation of `AssociatedGammaStatement`, if moreover `S_v`, `S'_v` are unitary and
`Π_v`, `Π'_v` are tempered, then `L(Π_v × Π'_v) = L(S_v ⊗ S'_v)`,
`L(Π_v^∨ × Π'^∨_v) = L(S_v^∨ ⊗ S'^∨_v)` and `ε(Π_v × Π'_v, ψ_v) = ε(S_v ⊗ S'_v, ψ_v)`. -/
def AssociatedTemperedFactorStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)]
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

/-- Henniart (2000), Théorème 2.4: if `S` is irreducible and unitary, `T` has unitary
central character, and `S` is weakly associated with the cuspidal class of `T`, then at
every finite place `v`, every irreducible local component `Π_v` of every spectral
presentation is equivalent to `i(σ_1, …, σ_k)`, the normalized parabolic induction of
unitarizable supercuspidal representations `σ_i` of `GL_{n_i}(F_v)`. -/
def AssociatedSupercuspidalInductionStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)]
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

/-- Henniart (2000), Corollaire 2.4: for irreducible unitary `S`, `S'` weakly associated
with cuspidal classes of unitary central character, at every finite place `v`,
`L(Π_v × Π'_v) = L(S_v ⊗ S'_v)`, `L(Π_v^∨ × Π'^∨_v) = L(S_v^∨ ⊗ S'^∨_v)` and
`ε(Π_v × Π'_v, ψ_v) = ε(S_v ⊗ S'_v, ψ_v)`, with no local hypothesis at `v`. -/
def AssociatedCuspidalFactorStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)]
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

/-- Henniart (2000), Théorèmes 2.3 and 2.4 with their corollaries: the conjunction of the
four statements above, at common universe levels. -/
def AssociatedFactorStatement : Prop :=
  AssociatedGammaStatement.{u, uV, uP, uQ, uE} ∧
    AssociatedTemperedFactorStatement.{u, uV, uP, uQ, uE} ∧
      AssociatedSupercuspidalInductionStatement.{u, uV, uP, uQ} ∧
        AssociatedCuspidalFactorStatement.{u, uV, uP, uQ, uE}

end RelativeWeilGroup

end Langlands.ClassField.Global
