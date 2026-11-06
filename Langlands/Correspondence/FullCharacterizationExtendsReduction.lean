import Langlands.Correspondence.FullCharacterizationStatement
import Langlands.Correspondence.RankOneComparison
import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Weil.Representation.CharacterNormalizationProof
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Representation.RankinSelberg.LocalConverseStatement
import Langlands.Representation.RankinSelberg.PairLFactorCharacterizationStatement
import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.RankinSelberg.SupercuspidalLanglandsEpsilon
import Langlands.Correspondence.ZeroMonodromyExtension
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof
import Langlands.Correspondence.LowerRankWeilFactor
import Langlands.Correspondence.IrreducibleZeroMonodromy

/-!
# Henniart's extension argument, conditional on its deep inputs

Henniart 2002, Corollary 1.6, proof in Section 3.4: rank induction. Rank one
uses uniqueness of the reciprocity family. In rank at least two, Theorem 1.6(b)
and the lower-rank parameter criterion `L = 1` give supercuspidality, and the
local converse theorem with uniqueness of the local-constant system gives
equality with the supercuspidal map. The three inputs not yet proved in the
Library are explicit hypotheses, bundled as `FullCharacterizationExtendsInputs`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor LocalFactor.CommonClosure Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance extendsReductionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance extendsReductionGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

section Helpers

variable {F}

/-- The underlying pair class of a zero-monodromy parameter class is the
zero-monodromy pair class of the Weil class. -/
theorem IsZeroMonodromyOf.parameterForget_eq {n : ℕ+}
    {σ : IrreducibleWeilClass.{uF, uP} F n} {D : WeilDeligneClass.{uF, uP} F n}
    (h : IsZeroMonodromyOf F σ D) : parameterForget F D = weilPairClass F σ := by
  obtain ⟨A, hA, hAD⟩ := h
  rw [← hAD]
  unfold weilPairClass
  rw [← hA]
  rfl

/-- A rank-one Weil class and a rank-one parameter class given by the same
scalar character are related by zero monodromy. -/
theorem isZeroMonodromyOf_of_rankOne {χ : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ : IrreducibleWeilClass.{uF, uP} F 1} {D : WeilDeligneClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F χ σ) (hD : IsRankOneParameterCharacter F χ D) :
    IsZeroMonodromyOf F σ D := by
  obtain ⟨A, hA, ⟨a⟩⟩ := hσ
  obtain ⟨B, hB, ⟨b⟩⟩ := hD
  refine ⟨A, hA, ?_⟩
  rw [← hB]
  have z : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom A)
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom
        (FiniteRepresentation.of (Langlands.characterRepresentation χ))) :=
    ⟨a.symm, by
      ext x
      change a.symm.toLinearMap 0 = 0
      exact map_zero _⟩
  exact (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr ⟨z.trans b⟩

end Helpers

/-- Base components of one reciprocity family give one reciprocity homomorphism:
the base Weil subgroup is the whole Weil group. -/
theorem reciprocityHom_eq_of_isBaseReciprocity {e e' : ReciprocityCandidate F}
    {eC : ReciprocityFamily F} (h : IsBaseReciprocity F e eC)
    (h' : IsBaseReciprocity F e' eC) : reciprocityHom F e = reciprocityHom F e' := by
  have htop : weilSubgroup F (baseExtension F) = ⊤ := by
    change Subgroup.comap _ (⊥ : IntermediateField F.Carrier
      (AlgebraicClosure F.Carrier)).fixingSubgroup = ⊤
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.comap_top _
  ext g
  have hg : g ∈ weilSubgroup F (baseExtension F) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact (h ⟨g, hg⟩).symm.trans (h' ⟨g, hg⟩)

/-- Rank one: if `τ` and `c0` are rank-one compatible for candidates with the
same Weil characters, then `τ` sends the zero-monodromy class of each rank-one
Weil class `σ` to `c0 σ`. -/
theorem rankOne_eq_of_weilCharacter_eq {e e0 : ReciprocityCandidate F}
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {τ : FullMap.{uF, uP, uA} F}
    (hwc : ∀ χ : QuasiCharacter F, weilCharacter F e χ = weilCharacter F e0 χ)
    (hone0 : SupercuspidalRankOneCompatibility F e0 c0)
    (hone : RankOneCompatibility F e τ)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) (D : WeilDeligneClass.{uF, uP} F 1)
    (hD : IsZeroMonodromyOf F σ D) :
    τ 1 D = supercuspidalToAutomorphic F (c0 1 σ) := by
  obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F e0 σ
  obtain ⟨σ1, hσ1, hπ1⟩ := hone0 χ
  have hσσ : σ1 = σ := IsRankOneWeilCharacter.class_unique F hσ1 hσ
  subst hσσ
  obtain ⟨D1, hD1, hτ1⟩ := hone χ
  rw [hwc χ] at hD1
  have hDD : D1 = D := (isZeroMonodromyOf_of_rankOne hσ1 hD1).unique hD
  subst hDD
  exact IsRankOneCharacter.class_unique F hτ1 hπ1

/-- Henniart 2002, Corollary 1.6, conditional on the local converse theorem,
Theorem 1.6(b), uniqueness of local-constant systems, the lower-rank parameter
criterion `L = 1` and existence of zero-monodromy classes. Uniqueness of the
reciprocity family is the published `commonClosureReciprocityUniqueness`, and
agreement of Langlands and JPSS epsilon factors on supercuspidal pairs is proved
in `SupercuspidalLanglandsEpsilon`. -/
theorem extendsSupercuspidal_of_inputs
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hLchar : RankinSelberg.SupercuspidalLFactorCharacterizationStatement.{uF, uA, uA})
    (hsys : ∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {τ : FullMap.{uF, uP, uA} F}
    {ψ : NontrivialAdditiveCharacter F} {e : ReciprocityCandidate F}
    (hc0 : IsSupercuspidalCorrespondence F c0)
    (hone : RankOneCompatibility F e τ) (hfac : FullFactorCompatibilityAt F e ψ τ) :
    ExtendsSupercuspidal F c0 τ := by
  obtain ⟨hbij, -, e0, -, hone0, -, -, eC0, ε0, hε0, hbase0, hpair0⟩ := hc0
  obtain ⟨hL, eC, ε, hε, hbase, hepsτ⟩ := hfac
  have hfam : eC = eC0 :=
    LocalClassField.commonClosureReciprocityUniqueness.{uF} p F F.canonicalTopologicalData
      eC eC0 hε.1 hε0.1
  subst hfam
  have hεε : ε = ε0 := hsys eC ε ε0 hε hε0
  subst hεε
  have hwc : ∀ χ : QuasiCharacter F, weilCharacter F e χ = weilCharacter F e0 χ := by
    intro χ
    rw [weilCharacter_eq_comp, weilCharacter_eq_comp,
      reciprocityHom_eq_of_isBaseReciprocity F hbase hbase0]
  obtain ⟨ν, hν⟩ := hpair0.exists_selfDualMeasure F ψ
  have key : ∀ (m : ℕ) (σ : IrreducibleWeilClass.{uF, uP} F m.succPNat)
      (D : WeilDeligneClass.{uF, uP} F m.succPNat), IsZeroMonodromyOf F σ D →
        τ m.succPNat D = supercuspidalToAutomorphic F (c0 m.succPNat σ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero =>
        intro σ D hD
        exact rankOne_eq_of_weilCharacter_eq F hwc hone0 hone σ D hD
      | succ k =>
        intro σ D hD
        -- Lower-rank supercuspidal tests come from `c0` and the induction hypothesis.
        have test : ∀ r, r ≤ k →
            ∀ B : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := r + 1),
              ∃ (σ' : IrreducibleWeilClass.{uF, uP} F r.succPNat)
                (D' : WeilDeligneClass.{uF, uP} F r.succPNat),
                IsZeroMonodromyOf F σ' D' ∧
                  c0 r.succPNat σ' =
                    (Quotient.mk _ B : SupercuspidalAutomorphicClass.{uF, uA} F r.succPNat) ∧
                  τ r.succPNat D' =
                    automorphicClassOf F (n := r.succPNat) B.toIrreducibleAdmissible := by
          intro r hr B
          obtain ⟨σ', hσ'⟩ := (hbij r.succPNat).2
            (Quotient.mk _ B : SupercuspidalAutomorphicClass.{uF, uA} F r.succPNat)
          obtain ⟨D', hD'⟩ := exists_zeroMonodromyParameter F σ'
          refine ⟨σ', D', hD', hσ', ?_⟩
          rw [ih r (by omega) σ' D' hD', hσ']
          rfl
        obtain ⟨A, hA⟩ := automorphicClass_has_representative F (τ (k + 1).succPNat D)
        let J := SmoothRep.universeLift.{uF} A.obj
        have hJirr : J.IsIrreducible :=
          (SmoothRep.isIrreducible_universeLift_iff A.obj).mpr A.property.1
        have hJadm : J.IsAdmissible :=
          (SmoothRep.isAdmissible_universeLift_iff A.obj).mpr A.property.2
        -- Step A: supercuspidality from Theorem 1.6(b) and the criterion `L = 1`.
        have hJsc : GeneralLinear.IsSupercuspidal J.representation := by
          refine (hLchar p F ψ ⟨ν, hν⟩ k J hJirr hJadm).mpr ?_
          intro r hr ρ hρirr hρsc
          obtain ⟨S, hSirr, ⟨φ⟩⟩ :=
            padicIrreducibleSmoothSmallRealization.{uF, max uF uA, uA} p F
              F.canonicalTopologicalData (r + 1) ρ hρirr
          let B : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := r + 1) :=
            ⟨S, hSirr, GeneralLinear.isSupercuspidal_of_equiv φ hρsc⟩
          obtain ⟨σ', D', hD', -, hτD'⟩ := test r hr B
          obtain ⟨P, hP, hPL⟩ := (hL (k + 1) r D D').2 ν hν
          rw [hD.parameterForget_eq, hD'.parameterForget_eq,
            arithmeticPairLFactor_weilPairClass_eq_one F σ σ'
              (Nat.succ_lt_succ (by omega))] at hPL
          have hP1 : P = 1 := by
            have h1 : algebraMap ℂ[X] (RatFunc ℂ) P = 1 := by
              rw [eq_comm, inv_eq_one] at hPL
              exact hPL
            exact RatFunc.algebraMap_injective ℂ (h1.trans (map_one _).symm)
          subst hP1
          rw [← hA, hτD'] at hP
          have hJS := (isAutomorphicPairLPolynomial_iff F A B.toIrreducibleAdmissible J
            (SmoothRep.universeLift.{uF} S) (SmoothRep.universeLiftEquiv A.obj).symm
            (SmoothRep.universeLiftEquiv S).symm).mp hP
          exact (RankinSelberg.IsLanglandsPairLPolynomial.congr_equiv
            (Representation.Equiv.refl _)
            ((SmoothRep.universeLiftEquiv S).symm.trans φ.symm)).mp hJS
        have hAsc : GeneralLinear.IsSupercuspidal A.obj.representation :=
          GeneralLinear.isSupercuspidal_of_equiv (SmoothRep.universeLiftEquiv A.obj).symm hJsc
        let S0 : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := k + 1 + 1) :=
          ⟨A.obj, A.property.1, hAsc⟩
        have hτS : τ (k + 1).succPNat D = supercuspidalToAutomorphic F
            (Quotient.mk _ S0 : SupercuspidalAutomorphicClass.{uF, uA} F (k + 1).succPNat) :=
          hA.symm
        rw [hτS]
        congr 1
        -- Step B: equality from the local converse theorem.
        refine hconverse p F ψ ⟨ν, hν⟩ k _ _ ?_
        intro r hr t
        induction t using Quotient.inductionOn with
        | h B =>
          obtain ⟨σ', D', hD', hcB, hτD'⟩ := test r hr B
          obtain ⟨e1, he1, ha1⟩ := ((hpair0 ψ (k + 1) r σ σ').2 ν hν).2
          obtain ⟨e2, he2, ha2⟩ := (hepsτ (k + 1) r D D').2 ν hν
          rw [hD.parameterForget_eq, hD'.parameterForget_eq] at ha2
          have he12 : e2 = e1 := Prod.ext (ha2.unique F ha1).1 (ha2.unique F ha1).2
          subst he12
          refine ⟨e2, ?_, ?_⟩
          · rw [hτS, hτD'] at he2
            have hJB := (isAutomorphicPairEpsilonFactor_iff F A B.toIrreducibleAdmissible J
              (SmoothRep.universeLift.{uF} B.obj) (SmoothRep.universeLiftEquiv A.obj).symm
              (SmoothRep.universeLiftEquiv B.obj).symm).mp he2
            have hsym :=
              RankinSelberg.IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal
                hJsc (GeneralLinear.isSupercuspidal_of_equiv
                  (SmoothRep.universeLiftEquiv B.obj) B.property.2) hJB
            have hAB := (RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv
              (SmoothRep.universeLiftEquiv A.obj).symm
              (SmoothRep.universeLiftEquiv B.obj).symm).mp hsym
            exact (RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (by omega)).mp hAB
          · rw [hcB] at he1
            exact (isSupercuspidalPairEpsilonFactor_iff_class F ψ ν (by omega) _ _ e2).mp he1
  intro n σ
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, m.succPNat = n := ⟨n.natPred, PNat.succPNat_natPred n⟩
  obtain ⟨D, hD⟩ := exists_zeroMonodromyParameter F σ
  exact ⟨D, hD, key m σ D hD⟩

/-- The target statement, conditional on the same inputs. -/
theorem fullCharacterizationExtends_of_inputs
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hLchar : RankinSelberg.SupercuspidalLFactorCharacterizationStatement.{uF, uA, uA})
    (hsys : ∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC) :
    FullCharacterizationExtendsStatement.{uF, uP, uA} F := by
  intro c0 τ ψ e hc0 _ hone hfac
  exact extendsSupercuspidal_of_inputs F hconverse hLchar hsys
    hc0 hone hfac

/-- The three inputs of Henniart's extension argument that are not yet proved
in the Library: the supercuspidal local converse theorem, Theorem 1.6(b), and
uniqueness of local-constant systems for every reciprocity family of `F`. -/
def FullCharacterizationExtendsInputs : Prop :=
  RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA} ∧
    RankinSelberg.SupercuspidalLFactorCharacterizationStatement.{uF, uA, uA} ∧
    ∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC

/-- The target statement follows from the bundled inputs. -/
theorem FullCharacterizationExtendsInputs.fullCharacterizationExtends
    (h : FullCharacterizationExtendsInputs.{uF, uP, uA} F) :
    FullCharacterizationExtendsStatement.{uF, uP, uA} F :=
  fullCharacterizationExtends_of_inputs F h.1 h.2.1 h.2.2

end Langlands.Correspondence
