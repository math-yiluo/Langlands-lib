import Langlands.Global.Factors.CertifiedFactorSeparationStatement
import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.Classification.TemperedSmoothDualityProof
import Langlands.Representation.Classification.LanglandsDatumRealization
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Group.GL.OneBlockShape

/-! # Pole bounds for the certified L-polynomials of tempered pairs -/

noncomputable section

namespace Langlands

universe uF uV uW uA

open GeneralLinear PadicField.TopologicalData Polynomial

namespace PadicField.TopologicalData.TemperedLanglandsDatum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The single-block tempered Langlands datum with exponent zero. -/
def single {n : ℕ} (hn : 0 < n)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hρ : letI := T.topology; Representation.IsIrreducible ρ.representation)
    (htρ : letI := T.topology; T.IsTempered ρ.representation) :
    TemperedLanglandsDatum.{uV, uF} T n where
  shape := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  blocks := fun _ => ρ
  irreducible := fun _ => hρ
  tempered := fun _ => htρ
  exponent := fun _ => 0
  strictAnti := by
    change StrictAnti (fun _ : Fin 1 => (0 : ℝ))
    intro i j hij
    have heq : i = j := Subsingleton.elim _ _
    subst j
    exact (lt_irrefl _ hij).elim

/-- A tempered irreducible representation is presented by a single block at
exponent zero, with its standard module actually equivalent to the target. -/
theorem exists_zero_presentation {n : ℕ} (hn : 0 < n)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hρ : letI := T.topology; Representation.IsIrreducible ρ.representation)
    (htρ : letI := T.topology; T.IsTempered ρ.representation)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (e : letI := T.topology; ρ.representation.Equiv π.representation) :
    letI := T.topology
    ∃ d : TemperedLanglandsDatum.{uV, uF} T n,
      d.IsLanglandsQuotient π ∧
        Nonempty (d.standardModule.representation.Equiv π.representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let d := single hn ρ hρ htρ
  let τ := fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).representation
  let E := T.singleBlockNormalizedProductEquiv d.shape rfl τ
    (fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).isSmooth) ⟨0, Nat.one_pos⟩
  have hτ : τ ⟨0, Nat.one_pos⟩ = ρ.representation := by
    change twist (T.determinantPowerCharacter n 0) ρ.representation = ρ.representation
    rw [show T.determinantPowerCharacter n 0 = 1 from realPowerCharacter_zero _]
    exact twist_one _
  let Eρ := equivOfRepresentationEq hτ
  let E' := E.trans ((Representation.Equiv.mk Eρ.toLinearEquiv
    (fun g => Eρ.isIntertwining' _)).trans (T.castRankEquiv rfl ρ))
  let Eπ : d.standardModule.representation.Equiv π.representation := E'.trans e
  exact ⟨d, ⟨(isIrreducible_iff_of_equiv e).mp hρ,
    Eπ.toIntertwiningMap, Eπ.surjective⟩, ⟨Eπ⟩⟩

end PadicField.TopologicalData.TemperedLanglandsDatum

namespace RankinSelberg

open HarmonicAnalysis MeasureTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- On tempered irreducibles, the classification certificate is a certificate
for the actual pair itself. Both block universes are retained. -/
theorem IsLanglandsPairLPolynomial.symmetric_of_tempered
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier}
    {r t : ℕ}
    {π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    {σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)}
    {P : ℂ[X]} (hP : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P)
    (hπ : Representation.IsIrreducible π.representation)
    (htπ : F.canonicalTopologicalData.IsTempered π.representation)
    (hσ : Representation.IsIrreducible σ.representation)
    (htσ : F.canonicalTopologicalData.IsTempered σ.representation) :
    IsPadicSymmetricLPolynomial F ψ ν π.representation σ.representation P := by
  obtain ⟨ρ, hρ, ⟨eρ⟩⟩ := padicIrreducibleSmoothSmallRealization.{uF, max uF uV, uV}
    p F F.canonicalTopologicalData (r + 1) π hπ
  obtain ⟨τ, hτ, ⟨eτ⟩⟩ := padicIrreducibleSmoothSmallRealization.{uF, max uF uW, uW}
    p F F.canonicalTopologicalData (t + 1) σ hσ
  obtain ⟨d, hd, ⟨ed⟩⟩ := TemperedLanglandsDatum.exists_zero_presentation r.succ_pos
    ρ hρ ((F.canonicalTopologicalData.isTempered_iff_of_equiv eρ).mp htπ) π eρ.symm
  obtain ⟨e, he, ⟨ee⟩⟩ := TemperedLanglandsDatum.exists_zero_presentation t.succ_pos
    τ hτ ((F.canonicalTopologicalData.isTempered_iff_of_equiv eτ).mp htσ) σ eτ.symm
  exact (IsPadicSymmetricLPolynomial.congr_equiv ed ee).mp (hP.2.2 d e hd he)

/-- The closed tempered product theorem applies to arbitrary positive block
sizes and retains its open-unit-disk nonvanishing conclusion. -/
theorem temperedBlockInduction_poleFree
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j))
    (hiπ : ∀ i, Representation.IsIrreducible (π i))
    (hsπ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i))
    (hiσ : ∀ j, Representation.IsIrreducible (σ j))
    (hsσ : ∀ j, F.canonicalTopologicalData.IsSquareIntegrable (σ j)) :
    ∃ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced B π)
      (F.canonicalNormalizedProductInduced C σ) P ∧
      ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 := by
  classical
  rcases B with ⟨k, m, hmpos, hm⟩
  rcases C with ⟨l, n, hnpos, hn⟩
  choose m' hm' using fun i => Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hmpos i))
  choose n' hn' using fun j => Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hnpos j))
  have hmfun : m = fun i => m' i + 1 := funext hm'
  have hnfun : n = fun j => n' j + 1 := funext hn'
  subst m n
  obtain ⟨P, Q, hP, hQ, hprod, hfree⟩ :=
    temperedLFactor.{uF, uV, uW} p F ψ ν r t k l m' n' hm hn π σ hiπ hsπ hiσ hsσ
  exact ⟨P, hP, hfree⟩

/-- Every symmetric L-polynomial of irreducible tempered representations has
no zero in the open unit disk. -/
theorem IsPadicSymmetricLPolynomial.poleFree_of_tempered
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ}
    {π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    {σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)}
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      π.representation σ.representation P)
    (hπ : Representation.IsIrreducible π.representation)
    (htπ : F.canonicalTopologicalData.IsTempered π.representation)
    (hσ : Representation.IsIrreducible σ.representation)
    (htσ : F.canonicalTopologicalData.IsTempered σ.representation) :
    ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 := by
  obtain ⟨B, b, hb, ⟨eb⟩⟩ := Classification.temperedBlockExhaustion.{uF, uV}
    F F.canonicalTopologicalData (r + 1) r.succ_pos π hπ htπ
  obtain ⟨C, c, hc, ⟨ec⟩⟩ := Classification.temperedBlockExhaustion.{uF, uW}
    F F.canonicalTopologicalData (t + 1) t.succ_pos σ hσ htσ
  obtain ⟨P₀, hP₀, hfree⟩ := temperedBlockInduction_poleFree ψ ν B C
    (fun i => (b i).representation) (fun j => (c j).representation)
    (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun j => (hc j).1) (fun j => (hc j).2.1)
  have hPe := (IsPadicSymmetricLPolynomial.congr_equiv
    (SmoothRep.equivOfIso eb) (SmoothRep.equivOfIso ec)).mp hP
  rw [hPe.unique hP₀]
  exact hfree

/-- The L-polynomial defined through the Langlands classification is pole-free
for an irreducible tempered pair, without a genericity premise. -/
theorem IsLanglandsPairLPolynomial.poleFree_of_tempered
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ}
    {π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)}
    {σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)}
    {P : ℂ[X]} (hP : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P)
    (hπ : Representation.IsIrreducible π.representation)
    (htπ : F.canonicalTopologicalData.IsTempered π.representation)
    (hσ : Representation.IsIrreducible σ.representation)
    (htσ : F.canonicalTopologicalData.IsTempered σ.representation) :
    ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 :=
  (hP.symmetric_of_tempered hπ htπ hσ htσ).poleFree_of_tempered ν hπ htπ hσ htσ

end RankinSelberg

namespace Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance generalLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance generalLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The class L-polynomial of two actual tempered irreducible admissible
objects has no zero in the open unit disk. -/
theorem IsAutomorphicPairLPolynomial.poleFree_of_tempered
    {ψ : NontrivialAdditiveCharacter F} {ν : LocalAdditiveHaarMeasure F}
    (hν : IsSelfDualMeasure F ψ ν) {r t : ℕ}
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (B : AutomorphicObject.{uF, uA} F t.succPNat)
    (htA : F.canonicalTopologicalData.IsTempered A.obj.representation)
    (htB : F.canonicalTopologicalData.IsTempered B.obj.representation)
    {P : ℂ[X]} (hP : IsAutomorphicPairLPolynomial F ψ ν
      (automorphicClassOf F A) (automorphicClassOf F B) P) :
    ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 := by
  obtain ⟨C, D, J, K, hC, hD, ⟨eJ⟩, ⟨eK⟩, hP⟩ := hP
  obtain ⟨eC⟩ := (automorphicClassOf_eq_iff F C A).mp hC
  obtain ⟨eD⟩ := (automorphicClassOf_eq_iff F D B).mp hD
  let a := eJ.trans eC
  let b := eK.trans eD
  exact hP.poleFree_of_tempered ⟨ν, hν⟩
    ((isIrreducible_iff_of_equiv a).mpr A.property.1)
    ((F.canonicalTopologicalData.isTempered_iff_of_equiv a).mpr htA)
    ((isIrreducible_iff_of_equiv b).mpr B.property.1)
    ((F.canonicalTopologicalData.isTempered_iff_of_equiv b).mpr htB)

/-- Every actual representative of a smooth dual class of a tempered object
is tempered. -/
theorem IsSmoothDual.tempered_representative {n : ℕ+}
    (A B : AutomorphicObject.{uF, uA} F n)
    (hdual : IsSmoothDual F (automorphicClassOf F A) (automorphicClassOf F B))
    (htA : F.canonicalTopologicalData.IsTempered A.obj.representation) :
    F.canonicalTopologicalData.IsTempered B.obj.representation := by
  obtain ⟨C, D, hC, hD, ⟨e⟩⟩ := hdual
  obtain ⟨eC⟩ := (automorphicClassOf_eq_iff F C A).mp hC
  obtain ⟨eD⟩ := (automorphicClassOf_eq_iff F D B).mp hD
  have htC := (F.canonicalTopologicalData.isTempered_iff_of_equiv eC).mpr htA
  exact (F.canonicalTopologicalData.isTempered_iff_of_equiv (e.trans eD)).mp
    htC.smoothContragredient

end Correspondence

namespace Global.GLPoleRegion

/-- Open-unit-disk nonvanishing on both polynomials separates the original
zeros from reflected dual zeros at any residue cardinality greater than one. -/
theorem hasNoReflectedCommonZero_of_poleFree {q : ℕ} (hq : 1 < q)
    {P Pd : ℂ[X]}
    (hP : ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0)
    (hPd : ∀ z : ℂ, ‖z‖ < 1 → Pd.eval z ≠ 0) :
    HasNoReflectedCommonZero q P Pd := by
  intro z hz hzero
  have hz1 : 1 ≤ ‖z‖ := le_of_not_gt (fun hlt => hP z hlt hzero.1)
  have hqR : 1 < (q : ℝ) := by exact_mod_cast hq
  have hreflect : ‖(q : ℂ)⁻¹ * z⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, norm_inv, Complex.norm_natCast]
    calc
      (q : ℝ)⁻¹ * ‖z‖⁻¹ ≤ (q : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hz1)
          (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hqR)))
      _ < 1 := by simpa only [mul_one] using inv_lt_one_of_one_lt₀ hqR
  exact hPd _ hreflect hzero.2

end Global.GLPoleRegion

namespace Global.FactorSeparation

open Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance generalLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Temperedness of the original objects certifies no reflected cancellation
for every pair of their smooth dual classes and every supplied L-polynomial. -/
theorem certifiedAutomorphicPoleRegions_of_tempered
    (ψ : NontrivialAdditiveCharacter F) {r t : ℕ}
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (B : AutomorphicObject.{uF, uA} F t.succPNat)
    (htA : F.canonicalTopologicalData.IsTempered A.obj.representation)
    (htB : F.canonicalTopologicalData.IsTempered B.obj.representation) :
    CertifiedAutomorphicPoleRegions F ψ (automorphicClassOf F A) (automorphicClassOf F B) := by
  intro ν hν πd πd' P Pd hd hd' hP hPd
  obtain ⟨Ad, hAd⟩ := automorphicClass_has_representative F πd
  obtain ⟨Bd, hBd⟩ := automorphicClass_has_representative F πd'
  rw [← hAd] at hd hPd
  rw [← hBd] at hd' hPd
  exact GLPoleRegion.hasNoReflectedCommonZero_of_poleFree
    F.canonicalTopologicalData.residueCardinality_gt_one
    (hP.poleFree_of_tempered F hν A B htA htB)
    (hPd.poleFree_of_tempered F hν Ad Bd
      (hd.tempered_representative F A Ad htA) (hd'.tempered_representative F B Bd htB))

end Global.FactorSeparation

end Langlands
