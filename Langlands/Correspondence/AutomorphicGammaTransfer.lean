import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Automorphic.AssociatedContragredientStatement

/-! # Uniqueness and order transfer for certified automorphic gamma factors -/

noncomputable section

open scoped Topology

namespace Langlands.Correspondence

universe uF uA

open LocalFactor RankinSelberg Polynomial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : NontrivialAdditiveCharacter F} {ν : LocalAdditiveHaarMeasure F}
  {r t : ℕ}
  {π πd : AutomorphicClass.{uF, uA} F r.succPNat}
  {π' πd' : AutomorphicClass.{uF, uA} F t.succPNat}

/-- Supplied genuine dual and pair-factor certificates construct a certified
rational gamma factor, without an assertion that such inputs always exist. -/
def automorphicPairGammaFactor
    (hd : IsSmoothDual F π πd) (hd' : IsSmoothDual F π' πd')
    {P Pd : ℂ[X]} {e : ℂˣ × ℤ}
    (hP : IsAutomorphicPairLPolynomial F ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor F ψ ν π π' e) :
    {G : RatFunc ℂ // IsAutomorphicPairGammaFactor F ψ ν π π' G} :=
  ⟨rationalGammaExpression (residueReflection F) e.1 e.2 P Pd,
    πd, πd', P, Pd, e, hd, hd', hP, hPd, he, rfl⟩

/-- A class pair has at most one certified rational gamma factor. -/
theorem IsAutomorphicPairGammaFactor.unique
    {G H : RatFunc ℂ}
    (hG : IsAutomorphicPairGammaFactor F ψ ν π π' G)
    (hH : IsAutomorphicPairGammaFactor F ψ ν π π' H) : G = H := by
  obtain ⟨δ, δ', P, Pd, e, hd, hd', hP, hPd, he, hH⟩ := hH
  exact (hG.eq_rationalGammaExpression hd hd' hP hPd he).trans hH.symm

/-- Two certified values, including certificates constructed from different
factor witnesses, are equal as elements of the subtype. -/
theorem automorphicPairGammaFactor_subsingleton :
    Subsingleton {G : RatFunc ℂ // IsAutomorphicPairGammaFactor F ψ ν π π' G} :=
  ⟨fun G H => Subtype.ext (G.property.unique H.property)⟩

/-- Rational spectral evaluation of any certified automorphic gamma factor is
meromorphic at every point, including a pole or a cancelled singularity. -/
theorem IsAutomorphicPairGammaFactor.meromorphicAt
    {G : RatFunc ℂ} (hG : IsAutomorphicPairGammaFactor F ψ ν π π' G) (s : ℂ) :
    MeromorphicAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) s := by
  obtain ⟨δ, δ', P, Pd, e, hd, hd', hP, hPd, he, hGeq⟩ := hG
  have hgerm :=
    (show IsAutomorphicPairGammaFactor F ψ ν π π' G from
      ⟨δ, δ', P, Pd, e, hd, hd', hP, hPd, he, hGeq⟩).rationalSpectralValue_eventuallyEq
        hd hd' hP hPd he s
  exact (meromorphicAt_polynomialGammaExpression
    F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one e.1 e.2 P Pd s).congr hgerm.symm

end Langlands.Correspondence

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uP uQ uE

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Correspondence LocalFactor LocalFactor.CommonClosure

section Local

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}
  {eC : ReciprocityFamily K} {ε : NonabelianSystem.Assignment.{u, uE} K}
  {hε : NonabelianSystem.IsSystem K eC ε} {ψ : NontrivialAdditiveCharacter K}
  {ν : LocalAdditiveHaarMeasure K} {r t : ℕ}
  {π : AutomorphicClass.{u, u} K r.succPNat}
  {π' : AutomorphicClass.{u, u} K t.succPNat}
  {X Y : LocalPairClass.{u, uV} K} {G : RatFunc ℂ}

/-- A supplied gamma match identifies every certified automorphic gamma
factor with an arithmetic gamma factor for the same system and measure. -/
theorem IsPairGammaMatch.isArithmeticPairGammaFactor
    (hmatch : IsPairGammaMatch K eC ε hε ψ π π' X Y)
    (hν : IsSelfDualMeasure K ψ ν)
    (hG : IsAutomorphicPairGammaFactor K ψ ν π π' G) :
    IsArithmeticPairGammaFactor K eC ε hε ψ X Y G := by
  obtain ⟨H, hHa, hHw⟩ := hmatch.2 ν hν
  exact hG.unique hHa ▸ hHw

/-- A match with a unitary arithmetic pair transfers the order bound to any
certified automorphic gamma factor; no extra factor witnesses are required. -/
theorem IsPairGammaMatch.rationalSpectralValue_order_nonpos
    {A B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K}
    (hmatch : IsPairGammaMatch K eC ε hε ψ π π'
      (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B))
    (hν : IsSelfDualMeasure K ψ ν)
    (hG : IsAutomorphicPairGammaFactor K ψ ν π π' G)
    (hA : A.toFiniteRepresentation.IsUnitary) (hB : B.toFiniteRepresentation.IsUnitary)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue K.canonicalTopologicalData.residueCardinality G) s ≤ 0 :=
  (hmatch.isArithmeticPairGammaFactor hν hG).order_nonpos_of_isUnitary hA hB s hs

end Local

section SelfPair

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- For an actual relative Weil self-pair match, the order bound applies to
every supplied certified automorphic gamma factor. -/
theorem localSelfPair_rationalSpectralValue_order_nonpos
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)}
    {ν : LocalAdditiveHaarMeasure (padicField v)} {r t : ℕ}
    {π : AutomorphicClass.{u, u} (padicField v) r.succPNat}
    {π' : AutomorphicClass.{u, u} (padicField v) t.succPNat}
    {G : RatFunc ℂ}
    (hmatch : IsPairGammaMatch (padicField v) eC ε hε ψ π π'
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι))
    (hν : IsSelfDualMeasure (padicField v) ψ ν)
    (hG : IsAutomorphicPairGammaFactor (padicField v) ψ ν π π' G)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality G)
      s ≤ 0 :=
  localSelfPairGamma_order_nonpos ι hS (hmatch.isArithmeticPairGammaFactor hν hG) s hs

/-- A positive real order of a certified automorphic self-pair gamma factor
can occur only at zero, assuming the supplied actual self-pair match. -/
theorem localSelfPair_rationalSpectralValue_real_positive_order_only_zero
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)}
    {ν : LocalAdditiveHaarMeasure (padicField v)} {r t : ℕ}
    {π : AutomorphicClass.{u, u} (padicField v) r.succPNat}
    {π' : AutomorphicClass.{u, u} (padicField v) t.succPNat}
    {G : RatFunc ℂ}
    (hmatch : IsPairGammaMatch (padicField v) eC ε hε ψ π π'
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι))
    (hν : IsSelfDualMeasure (padicField v) ψ ν)
    (hG : IsAutomorphicPairGammaFactor (padicField v) ψ ν π π' G)
    (t₀ : ℝ)
    (ht₀ : 0 < meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality G)
      (t₀ : ℂ)) :
    t₀ = 0 :=
  localSelfPairGamma_real_positive_order_only_zero
    ι hS (hmatch.isArithmeticPairGammaFactor hν hG) t₀ ht₀

end SelfPair

section Global

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{u}} {r : ℕ}
  {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
  {T T' : Automorphic.CuspidalOperatorRealization F r}

/-- The supplied class-level dual association theorem transports association
to any actual full-operator cuspidal dual, in the same association universe. -/
theorem weaklyAssociated_dual_of_actual_contragredient
    (hdual : ClassContragredientAssociationStatement.{u, uV, uP, uP})
    (hT : T'.realization.IsContragredientOf T.realization)
    (hassoc : IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass) :
    IsWeaklyAssociatedClass.{u, uV, uP} (FiniteRepresentation.dual S) T'.isoClass :=
  hdual c F E S T.isoClass T'.isoClass
    ((Automorphic.CuspidalOperatorRealization.isoClass_isContragredientOf_iff T' T).mpr hT)
    hassoc

/-- Conditional global-to-local self-pair comparison, preserving the chosen
actual local actions of every supplied pair of spectral presentations. -/
theorem associatedSelfPairGammaMatch_of_actual_contragredient
    (hgamma : AssociatedGammaStatement.{u, uV, uP, uQ, uE})
    (hdual : ClassContragredientAssociationStatement.{u, uV, uP, uP})
    (hc : IsArithmeticClassFamily c)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (hT : T'.realization.IsContragredientOf T.realization)
    (hassoc : IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap v w.1 e ι)
    (ψv : NontrivialAdditiveCharacter (padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (eC : ReciprocityFamily (padicField v))
    (ε : NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : NonabelianSystem.IsSystem (padicField v) eC ε) :
    IsPairGammaMatch (padicField v) eC ε hε ψv
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι) :=
  hgamma c hc F E ψ hψ S (FiniteRepresentation.dual S) T T' hassoc
    (weaklyAssociated_dual_of_actual_contragredient hdual hT hassoc)
    P P' v hI hA hI' hA' w e ι hι ψv hψv eC ε hε

section Order

variable
    (hgamma : AssociatedGammaStatement.{u, uV, uP, uQ, uE})
    (hdual : ClassContragredientAssociationStatement.{u, uV, uP, uP})
    (hc : IsArithmeticClassFamily c)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (hT : T'.realization.IsContragredientOf T.realization)
    (hassoc : IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap v w.1 e ι)
    (ψv : NontrivialAdditiveCharacter (padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (eC : ReciprocityFamily (padicField v))
    (ε : NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : NonabelianSystem.IsSystem (padicField v) eC ε)
    {ν : LocalAdditiveHaarMeasure (padicField v)} {G : RatFunc ℂ}
    (hν : IsSelfDualMeasure (padicField v) ψv ν)
    (hG : IsAutomorphicPairGammaFactor (padicField v) ψv ν
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA') G)
    (hS : S.IsUnitary)

include hgamma hdual hc ψ hψ hT hassoc w e ι hι hψv eC ε hε hν hG hS

/-- The supplied global comparison theorems and actual cuspidal dual transfer
the unitary arithmetic bound to any certified local automorphic gamma factor. -/
theorem associatedSelfPairGamma_order_nonpos_of_actual_contragredient
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality G)
      s ≤ 0 := by
  have hmatch := associatedSelfPairGammaMatch_of_actual_contragredient
    hgamma hdual hc ψ hψ hT hassoc P P' v hI hA hI' hA' w e ι hι ψv hψv eC ε hε
  exact localSelfPair_rationalSpectralValue_order_nonpos ι hS hmatch hν hG s hs

/-- Under the same explicit global hypotheses, a positive order at a real
point of a certified automorphic self-pair factor forces that point to be zero. -/
theorem associatedSelfPairGamma_real_positive_order_only_zero_of_actual_contragredient
    (t₀ : ℝ)
    (ht₀ : 0 < meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality G)
      (t₀ : ℂ)) :
    t₀ = 0 := by
  have hmatch := associatedSelfPairGammaMatch_of_actual_contragredient
    hgamma hdual hc ψ hψ hT hassoc P P' v hI hA hI' hA' w e ι hι ψv hψv eC ε hε
  exact localSelfPair_rationalSpectralValue_real_positive_order_only_zero
    ι hS hmatch hν hG t₀ ht₀

end Order

end Global

end Langlands.ClassField.Global.RelativeWeilGroup
