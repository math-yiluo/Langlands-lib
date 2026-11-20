import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylCharacterMeasure

/-! # Conjugation and recentering of the source orbit measure -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 350000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean modelAffineHom modelAffine modelTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p q : SemistandardSpectralIndex i} {g : rationalPoints G}
  (hc : Association.ConjugatesLevi g p q) (m : LeviModel p) (n : LeviModel q)
  {A B : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
  (b : B.toGrp ⟶ n.scheme) (hb : IsSplitComponent b)
  [(m.splitCenter a).Normal] [(n.splitCenter b).Normal]
  [MeasurableSpace (levi p ⧸ m.splitCenter a)] [BorelSpace (levi p ⧸ m.splitCenter a)]
  [MeasurableSpace (levi q ⧸ n.splitCenter b)] [BorelSpace (levi q ⧸ n.splitCenter b)]
  (muP : Measure (levi p ⧸ m.splitCenter a)) (muQ : Measure (levi q ⧸ n.splitCenter b))
  [muP.IsHaarMeasure] [muQ.IsHaarMeasure]

set_option hygiene false in local notation "Ap" => m.splitCenter a
set_option hygiene false in local notation "Bq" => n.splitCenter b
set_option hygiene false in local notation "hAp" => m.splitCenter_le_center a ha
set_option hygiene false in local notation "hBq" => n.splitCenter_le_center b hb
set_option hygiene false in
local notation "eX" => Association.unitaryCharacterConjugation hc m n
set_option hygiene false in
local notation "eD" => Association.conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ
set_option hygiene false in local notation "XP" => unitaryUnramifiedCharacters m.normCharacters
set_option hygiene false in local notation "XQ" => unitaryUnramifiedCharacters n.normCharacters
set_option hygiene false in
local notation "DP" => DiscreteSeriesClass.{u, uV} Ap hAp muP
set_option hygiene false in
local notation "DQ" => DiscreteSeriesClass.{u, uV} Bq hBq muQ
set_option hygiene false in
local notation "OP" => discreteSeriesOrbit Ap hAp muP m.normCharacters
set_option hygiene false in
local notation "OQ" => discreteSeriesOrbit Bq hBq muQ n.normCharacters
set_option hygiene false in
local notation "SP" => discreteSeriesStabilizer Ap hAp muP m.normCharacters
set_option hygiene false in
local notation "SQ" => discreteSeriesStabilizer Bq hBq muQ n.normCharacters

variable (ω : DP)

/-- Character conjugation identifies exactly the two unramified self-twist subgroups. -/
theorem characterConjugation_map_stabilizer :
    (SP ω).map (eX).toMonoidHom = SQ (eD ω) := by
  have hinj : Function.Injective (eD : DP → DQ) := by
    intro x y hxy
    exact Subtype.ext ((SmoothDualClass.pullback_injective
      (Association.leviPointConjugation hc).symm) (congrArg Subtype.val hxy))
  ext χ
  obtain ⟨ψ, rfl⟩ := (eX).surjective χ
  refine (Subgroup.mem_map_iff_mem (f := (eX).toMulEquiv.toMonoidHom)
    (K := SP ω) (x := ψ) (eX).injective).trans ?_
  change ψ • ω = ω ↔ eX ψ • eD ω = eD ω
  rw [← Association.conjugateDiscreteSeriesClass_smul hc m n a ha b hb muP muQ]
  exact hinj.eq_iff.symm

/-- Actual conjugation on discrete-series classes at the conjugate base,
with the topology of the self-twist quotient. -/
def orbitConjugation : OP ω ≃ₜ OQ (eD ω) :=
  (discreteSeriesOrbitHomeomorph Ap hAp muP m.normCharacters ω).symm.trans
    ((quotientContinuousMulEquiv (eX) (SQ (eD ω)) (SP ω)
      (characterConjugation_map_stabilizer hc m n a ha b hb muP muQ ω)).toHomeomorph.trans
      (discreteSeriesOrbitHomeomorph Bq hBq muQ n.normCharacters (eD ω)))

set_option hygiene false in
local notation "eO" => orbitConjugation hc m n a ha b hb muP muQ ω

@[simp] theorem orbitConjugation_orbitMap (ψ : XP) :
    eO (discreteSeriesOrbitMap Ap hAp muP m.normCharacters ω ψ) =
      discreteSeriesOrbitMap Bq hBq muQ n.normCharacters (eD ω) (eX ψ) := by
  simp only [orbitConjugation, discreteSeriesOrbitMap,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rfl

@[simp] theorem orbitConjugation_val (x : OP ω) :
    (eO x).val = eD x.val := by
  obtain ⟨ψ, rfl⟩ :=
    (isOpenQuotientMap_discreteSeriesOrbitMap Ap hAp muP m.normCharacters ω).surjective x
  rw [orbitConjugation_orbitMap, discreteSeriesOrbitMap_val, discreteSeriesOrbitMap_val,
    Association.conjugateDiscreteSeriesClass_smul]

section Measure

variable [IsAffine A.X.left] [IsAffine B.X.left]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal]
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  (hindex' : (RenardCartan.splitValuationImage b).FiniteIndex)

/-- Conjugation preserves the orbit measure at the exact I.1 character
scale and with the reciprocal self-twist factor. -/
theorem normalizedOrbitMeasure_map_conjugation :
    Measure.map eO (normalizedOrbitMeasure m a ha hindex muP ω) =
      normalizedOrbitMeasure n b hb hindex' muQ (eD ω) := by
  let : Finite (SP ω) := finite_literalDiscreteSeriesStabilizer m a ha hindex muP ω
  let : Finite (SQ (eD ω)) :=
    finite_literalDiscreteSeriesStabilizer n b hb hindex' muQ (eD ω)
  let eS := ((SP ω).equivMapOfInjective (eX).toMonoidHom (eX).injective).trans
    (MulEquiv.subgroupCongr (characterConjugation_map_stabilizer hc m n a ha b hb muP muQ ω))
  have hcard : Nat.card (SP ω) = Nat.card (SQ (eD ω)) := Nat.card_congr eS.toEquiv
  rw [normalizedOrbitMeasure_eq_smul_map, normalizedOrbitMeasure_eq_smul_map, hcard,
    Measure.map_smul _ (eO).continuous.measurable.aemeasurable,
    Measure.map_map (eO).continuous.measurable
      (continuous_discreteSeriesOrbitMap Ap hAp muP m.normCharacters ω).measurable]
  have he : (eO) ∘ discreteSeriesOrbitMap Ap hAp muP m.normCharacters ω =
      discreteSeriesOrbitMap Bq hBq muQ n.normCharacters (eD ω) ∘ (eX) :=
    funext (orbitConjugation_orbitMap hc m n a ha b hb muP muQ ω)
  rw [he, ← Measure.map_map (f := (eX : XP → XQ))
    (continuous_discreteSeriesOrbitMap Bq hBq muQ n.normCharacters (eD ω)).measurable
    (eX).continuous.measurable,
    unitaryCharacterHaar_map_conjugation hc m n a ha b hb hindex hindex']

end Measure

section Recenter

variable {ω₁ ω₂ : DQ} (χ : XQ) (hχ : ω₁ = χ • ω₂)

include χ hχ in
/-- Recenter the target orbit at any base related by the displayed unitary twist. -/
def orbitRecenter : OQ ω₁ ≃ₜ OQ ω₂ := by
  subst ω₁
  exact discreteSeriesOrbitBaseChange Bq hBq muQ n.normCharacters ω₂ χ

omit [BorelSpace (levi q ⧸ n.splitCenter b)] in
@[simp] theorem orbitRecenter_val (x : OQ ω₁) :
    (orbitRecenter n b hb muQ χ hχ x).val = x.val := by
  subst ω₁
  rfl

variable [IsAffine B.X.left] [(rationalPoints.map b).range.Normal]
  (hindex' : (RenardCartan.splitValuationImage b).FiniteIndex)

/-- A unitary change of base retains the very same normalized orbit measure. -/
theorem normalizedOrbitMeasure_map_recenter :
    Measure.map (orbitRecenter n b hb muQ χ hχ)
      (normalizedOrbitMeasure n b hb hindex' muQ ω₁) =
    normalizedOrbitMeasure n b hb hindex' muQ ω₂ := by
  subst ω₁
  let : Finite (SQ ω₂) := finite_literalDiscreteSeriesStabilizer n b hb hindex' muQ ω₂
  let : Finite (SQ (χ • ω₂)) :=
    finite_literalDiscreteSeriesStabilizer n b hb hindex' muQ (χ • ω₂)
  rw [normalizedOrbitMeasure_eq, normalizedOrbitMeasure_eq]
  exact map_discreteSeriesOrbitMeasure_baseChange n.normCharacters Bq hBq muQ ω₂ χ
    (unitaryCharacterHaar n b hb hindex')

end Recenter

variable {ω' : DQ} (hω' : (Quotient.mk _ (eD ω) : OrbitClass n b hb muQ) = Quotient.mk _ ω')

/-- Actual conjugation to a target orbit presented using its own base point. -/
def orbitConjugationRecentered : OP ω ≃ₜ OQ ω' :=
  (eO).trans (orbitRecenter n b hb muQ (Quotient.exact hω').choose
    (Quotient.exact hω').choose_spec.symm)

@[simp] theorem orbitConjugationRecentered_val (x : OP ω) :
    (orbitConjugationRecentered hc m n a ha b hb muP muQ ω hω' x).val = eD x.val := by
  simp only [orbitConjugationRecentered, Homeomorph.trans_apply, orbitRecenter_val,
    orbitConjugation_val]

variable [IsAffine A.X.left] [IsAffine B.X.left]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal]
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  (hindex' : (RenardCartan.splitValuationImage b).FiniteIndex)

/-- The normalized measures correspond at any chosen target base. -/
theorem normalizedOrbitMeasure_map_conjugationRecentered :
    Measure.map (orbitConjugationRecentered hc m n a ha b hb muP muQ ω hω')
      (normalizedOrbitMeasure m a ha hindex muP ω) =
    normalizedOrbitMeasure n b hb hindex' muQ ω' := by
  change Measure.map ((orbitRecenter n b hb muQ (Quotient.exact hω').choose
      (Quotient.exact hω').choose_spec.symm) ∘ (eO)) _ = _
  rw [← Measure.map_map (Homeomorph.continuous _).measurable (eO).continuous.measurable,
    normalizedOrbitMeasure_map_conjugation]
  exact normalizedOrbitMeasure_map_recenter n b hb muQ _ _ hindex'

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure
