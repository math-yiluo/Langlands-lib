import Langlands.Representation.Classification.RankOneLanglandsStandardModule
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization

/-!
# Support lemmas for the supercuspidal characterization by L-factors of pairs

Helper results for Henniart 2002, Théorème 1.6(b).
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalLFactorCharacterization

open HarmonicAnalysis Whittaker GeneralLinear Derivative Polynomial
  Classification.SupercuspidalTopDerivative
  Classification.SupercuspidalDerivativesProof

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An irreducible supercuspidal representation of `GL_(0+n+1)(F)` has a nonzero
standard Whittaker functional: a nonzero functional on its one-dimensional top
derivative, pulled back along the top quotient map. -/
theorem hasFunctional_of_isSupercuspidal_zero_add
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (0 + n + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
        HasFunctional (N := upperUnipotent (0 + n + 1) F.Carrier)
          (θ := standardCharacter ψ (0 + n)) A.representation := by
  let _ := F.canonicalTopologicalData.topology
  intro A hirr hsc
  have hfin := finrank_generalLinearDerivativePositive_top F.canonicalTopologicalData ψ n A
    hirr hsc
  have := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨x, hx⟩ := exists_ne
    (0 : (generalLinearDerivativePositive F.canonicalTopologicalData ψ 0 n).obj A)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  refine ⟨⟨f ∘ₗ topQuotient F.canonicalTopologicalData ψ n A,
    comp_topQuotient_mem_glFunctionals F.canonicalTopologicalData ψ n A f⟩, ?_⟩
  intro h0
  obtain ⟨v, hv⟩ := topQuotient_surjective F.canonicalTopologicalData ψ n A x
  apply hf
  rw [← hv]
  exact LinearMap.congr_fun h0 v

/-- Gelfand-Kazhdan: an irreducible supercuspidal representation of `GL_(n+1)(F)`
is generic. -/
theorem isGeneric_of_isSupercuspidal
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier),
      Representation.IsIrreducible A.representation → IsSupercuspidal A.representation →
        IsGeneric ψ n A.representation := by
  let _ := F.canonicalTopologicalData.topology
  have key : ∀ m : ℕ,
      (∀ A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (m + 1) F.Carrier),
        A.IsIrreducible → IsSupercuspidal A.representation →
          HasFunctional (N := upperUnipotent (m + 1) F.Carrier)
            (θ := standardCharacter ψ m) A.representation) →
      ∀ A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (m + 1) F.Carrier),
        Representation.IsIrreducible A.representation → IsSupercuspidal A.representation →
          IsGeneric ψ m A.representation := fun m h A hirr hsc =>
    ⟨hirr, hsc.1, h A hirr hsc⟩
  exact key n ((Nat.zero_add n) ▸ hasFunctional_of_isSupercuspidal_zero_add F ψ n)

/-- An irreducible supercuspidal representation of `GL_(n+1)(F)` is of Whittaker
type. -/
theorem isOfWhittakerType_of_isSupercuspidal
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier),
      Representation.IsIrreducible A.representation → IsSupercuspidal A.representation →
        IsOfWhittakerType n (standardCharacter ψ n) A.representation := by
  let _ := F.canonicalTopologicalData.topology
  intro A hirr hsc
  exact isOfWhittakerType_of_isGeneric F (isGeneric_of_isSupercuspidal F ψ n A hirr hsc)


section Datum

variable (T : F.TopologicalData)

/-- Every irreducible smooth representation of `GL_n(F)`, `n > 0`, on a carrier in
`max uF uV` is a Langlands quotient of a tempered datum whose blocks have carriers
in `uV`: the published coverage gives a datum with blocks in `max uF uV`, and each
block has an equivalent irreducible realization in `uV`. -/
theorem exists_temperedLanglandsDatum_isLanglandsQuotient (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        ∃ d : T.TemperedLanglandsDatum.{uV, uF} n, d.IsLanglandsQuotient π := by
  let _ := T.topology
  intro π hπ
  obtain ⟨t, ht⟩ := Classification.temperedLanglandsQuotientCoverage.{uF, uV} F T n hn π hπ
  have hsmall := padicIrreducibleSmoothSmallRealization.{uF, max uF uV, uV} p F T
  choose σ hσ he using fun i => hsmall (t.shape.size i) (t.blocks i) (t.irreducible i)
  let d : T.TemperedLanglandsDatum.{uV, uF} n :=
    { shape := t.shape
      blocks := σ
      irreducible := hσ
      tempered := fun i =>
        (PadicField.TopologicalData.isTempered_iff_of_equiv (he i).some).mp (t.tempered i)
      exponent := t.exponent
      strictAnti := t.strictAnti }
  refine ⟨d, ?_⟩
  have e : t.standardModule.representation.Equiv d.standardModule.representation :=
    T.normalizedProductInducedEquiv t.shape (fun i => twistEquiv _ (he i).some)
  exact Classification.IsIrreducibleQuotient.of_equiv e ht

end Datum

section RankCast

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Reindexing along `finCongr rfl` is the identity. -/
theorem comp_reindex_finCongr_rfl {k : ℕ}
    (X : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V) :
    X.comp (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (rfl : k = k))).symm.toMonoidHom = X := by
  ext g v
  change X ((GeneralLinear.reindex (R := F.Carrier) (finCongr (rfl : k = k))).symm g) v = X g v
  have hg : (GeneralLinear.reindex (R := F.Carrier) (finCongr (rfl : k = k))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  rw [hg]

theorem isIrreducible_comp_reindex_iff {k N : ℕ} (h : k = N)
    (X : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V) :
    Representation.IsIrreducible (X.comp (GeneralLinear.reindex (R := F.Carrier)
        (finCongr h)).symm.toMonoidHom) ↔ Representation.IsIrreducible X := by
  subst h
  rw [comp_reindex_finCongr_rfl]

theorem isSupercuspidal_comp_reindex_iff {k N : ℕ} (h : k = N)
    (X : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    IsSupercuspidal (X.comp (GeneralLinear.reindex (R := F.Carrier)
        (finCongr h)).symm.toMonoidHom) ↔ IsSupercuspidal X := by
  subst h
  rw [comp_reindex_finCongr_rfl]

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem isPadicRankLPolynomial_comp_reindex_iff {m k N : ℕ} (h : k = N)
    (Z : Representation ℂ (Langlands.GeneralLinear m F.Carrier) W)
    (X : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V) {P : ℂ[X]} :
    IsPadicRankLPolynomial F ψ ν Z (X.comp (GeneralLinear.reindex (R := F.Carrier)
        (finCongr h)).symm.toMonoidHom) P ↔ IsPadicRankLPolynomial F ψ ν Z X P := by
  subst h
  rw [comp_reindex_finCongr_rfl]

/-- The rank L-relation is invariant under an equivalence of the second argument. -/
theorem isPadicRankLPolynomial_congr_right {m t : ℕ} {V₂ : Type*} [AddCommGroup V₂]
    [Module ℂ V₂]
    (Z : Representation ℂ (Langlands.GeneralLinear m F.Carrier) W)
    {X : Representation ℂ (Langlands.GeneralLinear t F.Carrier) V}
    {X₂ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) V₂}
    (φ : X.Equiv X₂) {P : ℂ[X]} :
    IsPadicRankLPolynomial F ψ ν Z X P ↔ IsPadicRankLPolynomial F ψ ν Z X₂ P := by
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    cases t with
    | zero => exact Iff.rfl
    | succ t =>
      exact IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl Z) φ

/-- An L-polynomial of arbitrary ranks has constant term `1`. -/
theorem IsPadicRankLPolynomial.coeff_zero' {m t : ℕ}
    {Z : Representation ℂ (Langlands.GeneralLinear m F.Carrier) W}
    {X : Representation ℂ (Langlands.GeneralLinear t F.Carrier) V} {P : ℂ[X]}
    (h : IsPadicRankLPolynomial F ψ ν Z X P) : P.coeff 0 = 1 := by
  cases m with
  | zero => exact h.elim
  | succ m =>
    cases t with
    | zero => exact h.elim
    | succ t => exact IsPadicSymmetricLPolynomial.coeff_zero h

end RankCast

section SingleBlock

variable {T : F.TopologicalData}

/-- The standard module of a one-block tempered datum is its twisted block,
transported to the ambient rank. -/
def singleBlockStandardModuleEquiv {n : ℕ} (d : T.TemperedLanglandsDatum.{uV, uF} n)
    (hB : d.shape.length = 1) (i : Fin d.shape.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    d.standardModule.representation.Equiv
      ((T.twistedBlocks d.shape d.blocks d.exponent i).representation.comp
        (GeneralLinear.reindex (R := F.Carrier)
          (finCongr (d.shape.singleBlock_size hB i))).symm.toMonoidHom) :=
  letI := T.topology
  T.singleBlockNormalizedProductEquiv d.shape hB
    (fun j => (T.twistedBlocks d.shape d.blocks d.exponent j).representation)
    (fun j => (T.twistedBlocks d.shape d.blocks d.exponent j).isSmooth) i

end SingleBlock

end Langlands.RankinSelberg.SupercuspidalLFactorCharacterization
