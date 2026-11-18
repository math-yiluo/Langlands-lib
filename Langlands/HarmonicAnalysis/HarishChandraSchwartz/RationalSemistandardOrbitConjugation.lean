import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSplitCenterIndependenceProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Analysis.HaarLpProof

/-! # Conjugation of actual semistandard discrete-series orbits -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

attribute [local instance] SourceMeasure.modelAffineHom SourceMeasure.modelAffine
  SourceMeasure.modelTopology

section Models

variable {p q : SemistandardSpectralIndex i} {g : rationalPoints G}
  (hc : ConjugatesLevi g p q) (m : LeviModel p) (n : LeviModel q)

/-- The same representing group with its inclusion conjugated in the ambient group. -/
def conjugateLeviModel : LeviModel q where
  scheme := m.scheme
  inclusion := m.inclusion ≫ (G.innerIso g).hom
  represents := ⟨by
    have : IsClosedImmersion (m.inclusion ≫ (G.innerIso g).hom).hom.hom.left :=
      m.closed.comp_iso (G.innerIso g)
    exact Over.mono_of_mono_left _, by
    rw [SubgroupFunctor.range_comp_iso, m.represents.2]
    exact (SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp hc⟩
  closed := m.closed.comp_iso (G.innerIso g)
  reductive := m.reductive

local notation "mt" => conjugateLeviModel hc m
local notation "eL" => leviPointConjugation hc

@[simp] theorem conjugateLeviModel_pointHomeomorph (z : rationalPoints m.scheme) :
    (mt).pointHomeomorph z = eL (m.pointHomeomorph z) := by
  apply Subtype.ext
  change rationalPoints.map (m.inclusion ≫ (G.innerIso g).hom) z =
    (eL (m.pointHomeomorph z) : rationalPoints G)
  rw [leviPointConjugation_apply, LeviModel.pointHomeomorph_coe]
  calc
    _ = rationalPoints.map (G.innerIso g).hom (rationalPoints.map m.inclusion z) := by
      simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
    _ = _ := by rw [rationalPoints_map_innerIso]; rfl

theorem conjugateLeviModel_normCharacters (χ : rationalCharacters m.scheme) :
    (mt).normCharacters χ = (m.normCharacters χ).comp (eL).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro y
  have hy : (mt).pointHomeomorph.symm y = m.pointHomeomorph.symm ((eL).symm y) := by
    apply (mt).pointHomeomorph.injective
    rw [ContinuousMulEquiv.apply_symm_apply, conjugateLeviModel_pointHomeomorph,
      ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  change (rationalNormCharacters m.scheme χ).toMul ((mt).pointHomeomorph.symm y) =
    (rationalNormCharacters m.scheme χ).toMul (m.pointHomeomorph.symm ((eL).symm y))
  rw [hy]

private theorem unitaryConjugation_subgroup_eq :
    unitaryUnramifiedCharacters (fun j => (m.normCharacters j).comp (eL).symm.toMonoidHom) =
      unitaryUnramifiedCharacters n.normCharacters := by
  have he := funext (conjugateLeviModel_normCharacters hc m)
  rw [← he]
  exact (mt).unitaryCharacters_eq n

/-- The actual conjugation homeomorphism on all unitary character parameters. -/
def unitaryCharacterConjugation :
    unitaryUnramifiedCharacters m.normCharacters ≃ₜ* unitaryUnramifiedCharacters n.normCharacters :=
  (unitaryUnramifiedCharactersHomeomorph eL m.normCharacters).trans
    (RepresentedParabolic.subgroupCongrContinuous (unitaryConjugation_subgroup_eq hc m n))

@[simp] theorem unitaryCharacterConjugation_apply
    (χ : unitaryUnramifiedCharacters m.normCharacters) (y : levi q) :
    (unitaryCharacterConjugation hc m n χ).val y = χ.val ((eL).symm y) := rfl

/-- The actual split-center point images correspond under Levi conjugation. -/
theorem splitCenter_map_leviPointConjugation
    {A B : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
    (b : B.toGrp ⟶ n.scheme) (hb : IsSplitComponent b) :
    (m.splitCenter a).map (eL).toMonoidHom = n.splitCenter b := by
  calc
    _ = (mt).splitCenter a := by
      unfold LeviModel.splitCenter
      rw [Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro z
      change eL (m.pointHomeomorph z) = (mt).pointHomeomorph z
      exact (conjugateLeviModel_pointHomeomorph hc m z).symm
    _ = n.splitCenter b := splitCenterChoiceIndependence q mt n A B a b ha hb

end Models

section Haar

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A : Subgroup H} [A.Normal] (hA : A ≤ Subgroup.center H)
  [MeasurableSpace (H ⧸ A)] [BorelSpace (H ⧸ A)]
  [LocallyCompactSpace (H ⧸ A)] [SecondCountableTopology (H ⧸ A)]

private theorem discreteSeriesClass_changeHaar
    (muP muQ : Measure (H ⧸ A)) [muP.IsHaarMeasure] [muQ.IsHaarMeasure]
    {ω : SmoothDualClass.{0, u, uV} (k := ℂ) (G := H)}
    (hω : IsDiscreteSeriesClass A hA muP ω) : IsDiscreteSeriesClass A hA muQ ω := by
  induction ω using Quotient.inductionOn with
  | h π =>
    rw [isDiscreteSeriesClass_mk] at hω ⊢
    obtain ⟨hadm, c, h⟩ := hω
    exact ⟨hadm, c, fun ℓ v => (haarMemLpInvariant (H ⧸ A) muP muQ _ 2).mp (h ℓ v)⟩

end Haar

section Orbits

variable {p q : SemistandardSpectralIndex i} {g : rationalPoints G}
  (hc : ConjugatesLevi g p q) (m : LeviModel p) (n : LeviModel q)
  {A B : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
  (b : B.toGrp ⟶ n.scheme) (hb : IsSplitComponent b)
  [(m.splitCenter a).Normal] [(n.splitCenter b).Normal]
  [MeasurableSpace (levi p ⧸ m.splitCenter a)] [BorelSpace (levi p ⧸ m.splitCenter a)]
  [MeasurableSpace (levi q ⧸ n.splitCenter b)] [BorelSpace (levi q ⧸ n.splitCenter b)]
  (muP : Measure (levi p ⧸ m.splitCenter a)) (muQ : Measure (levi q ⧸ n.splitCenter b))
  [muP.IsHaarMeasure] [muQ.IsHaarMeasure]

local notation "eL" => leviPointConjugation hc
local notation "Ap" => m.splitCenter a
local notation "Bq" => n.splitCenter b
local notation "hAp" => m.splitCenter_le_center a ha
local notation "hBq" => n.splitCenter_le_center b hb

local instance orbitLeviLocallyCompact (p : SemistandardSpectralIndex i) : LocallyCompactSpace (levi p) :=
  (isClosed_levi_of_model (chosenLeviModel p)).locallyCompactSpace

include ha hb in
omit [(m.splitCenter a).Normal] [(n.splitCenter b).Normal]
  [MeasurableSpace (levi p ⧸ m.splitCenter a)] [BorelSpace (levi p ⧸ m.splitCenter a)]
  [MeasurableSpace (levi q ⧸ n.splitCenter b)] [BorelSpace (levi q ⧸ n.splitCenter b)] in
private theorem splitCenter_map_leviPointConjugation_symm :
    (Bq).map (eL).symm.toMonoidHom = Ap :=
  (Subgroup.map_symm_eq_iff_map_eq (e := (eL).toMulEquiv) Ap).mpr
    (splitCenter_map_leviPointConjugation hc m n a ha b hb)

/-- The actual split-central quotient homeomorphism from the target back to the source. -/
def quotientLeviConjugationSymm : (levi q ⧸ Bq) ≃ₜ* (levi p ⧸ Ap) :=
  quotientContinuousMulEquiv (eL).symm Ap Bq
    (splitCenter_map_leviPointConjugation_symm hc m n a ha b hb)

local notation "eQ" => quotientLeviConjugationSymm hc m n a ha b hb

/-- Conjugate an actual discrete-series class, with the two given quotient Haar measures. -/
def conjugateDiscreteSeriesClass (ω : DiscreteSeriesClass.{u, uV} Ap hAp muP) :
    DiscreteSeriesClass.{u, uV} Bq hBq muQ := by
  let muTransport := Measure.map eQ muQ
  letI : muTransport.IsHaarMeasure := (eQ).isHaarMeasure_map muQ
  letI : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  letI : SecondCountableTopology (levi p) :=
    TopologicalSpace.Subtype.secondCountableTopology (levi p : Set (rationalPoints G))
  letI : SecondCountableTopology (levi p ⧸ Ap) := QuotientGroup.instSecondCountableTopology Ap
  exact DiscreteSeriesClass.pullback (eL).symm Ap hAp Bq hBq
    (splitCenter_map_leviPointConjugation_symm hc m n a ha b hb) muTransport muQ rfl
    ⟨ω.val, discreteSeriesClass_changeHaar hAp muP muTransport ω.property⟩

@[simp] theorem conjugateDiscreteSeriesClass_val (ω : DiscreteSeriesClass.{u, uV} Ap hAp muP) :
    (conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ ω).val =
      SmoothDualClass.pullback (eL).symm ω.val := rfl

theorem conjugateDiscreteSeriesClass_smul
    (χ : unitaryUnramifiedCharacters m.normCharacters) (ω : DiscreteSeriesClass.{u, uV} Ap hAp muP) :
    conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ (χ • ω) =
      unitaryCharacterConjugation hc m n χ • conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ ω := by
  apply Subtype.ext
  simp only [conjugateDiscreteSeriesClass_val, unitaryUnramified_smul_val]
  exact SmoothDualClass.pullback_twist (eL).symm _ _ _ _

/-- Conjugation on whole unitary unramified orbits of the actual discrete series. -/
def conjugateOrbit : OrbitClass.{u, uV} m a ha muP → OrbitClass.{u, uV} n b hb muQ :=
  Quotient.map (conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ) (by
    rintro ω ω' ⟨χ, hχ⟩
    refine ⟨unitaryCharacterConjugation hc m n χ, ?_⟩
    exact (conjugateDiscreteSeriesClass_smul hc m n a ha b hb muP muQ χ ω').symm.trans
      (congrArg (conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ) hχ))

@[simp] theorem conjugateOrbit_mk (ω : DiscreteSeriesClass.{u, uV} Ap hAp muP) :
    conjugateOrbit hc m n a ha b hb muP muQ (Quotient.mk _ ω) =
      Quotient.mk _ (conjugateDiscreteSeriesClass hc m n a ha b hb muP muQ ω) := rfl

end Orbits

section Intrinsic

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

variable (t : Θ) (q : SemistandardSpectralIndex i)
  {g : rationalPoints G} (hc : ConjugatesLevi g t.1 q)

/-- The full target index at the given parabolic after actual rational conjugation. -/
def conjugateFullIndex : Θ :=
  ⟨q, conjugateOrbit hc (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) t.2⟩

/-- The quotient orbit transport gives exactly the full transported constituent set. -/
theorem orbitConjugates_conjugateFullIndex :
    OrbitConjugates a ha mu g t (conjugateFullIndex a ha mu t q hc) := by
  let f := conjugateDiscreteSeriesClass hc (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
  let c := unitaryCharacterConjugation hc (chosenLeviModel t.1) (chosenLeviModel q)
  let o := conjugateOrbit hc (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
  refine ⟨hc, ?_⟩
  ext w
  constructor
  · rintro ⟨_, ⟨d, rfl, hd⟩, rfl⟩
    exact ⟨f d, rfl, congrArg o hd⟩
  · rintro ⟨d, rfl, hd⟩
    have he : Quotient.mk _ (f t.2.out) = o t.2 := congrArg o (Quotient.out_eq t.2)
    have hw : Quotient.mk _ d = o t.2 := hd
    obtain ⟨targetCharacter, htarget⟩ := Quotient.exact (hw.trans he.symm)
    obtain ⟨χ, hχ⟩ := c.surjective targetCharacter
    change targetCharacter • f t.2.out = d at htarget
    have hs := conjugateDiscreteSeriesClass_smul hc (chosenLeviModel t.1) (chosenLeviModel q)
      (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) χ t.2.out
    have hsd : f (χ • t.2.out) = d := hs.trans (hχ.symm ▸ htarget)
    refine ⟨(χ • t.2.out).val, ⟨χ • t.2.out, rfl, ?_⟩, congrArg Subtype.val hsd⟩
    refine Eq.trans ?_ (Quotient.out_eq t.2)
    exact Quotient.sound ⟨χ, rfl⟩

omit hc in
/-- Every actual Weyl conjugate Levi and target parabolic has a unique transported orbit. -/
theorem existsUnique_weylTransports_of_levi_eq
    (hM : torusCentralizer i ≤ t.1.levi) (w : relativeWeylGroup i)
    (hw : relativeWeylConjugateSubgroupFunctor i t.1.levi hM w = q.levi) :
    ∃! t' : Θ, t'.1 = q ∧ WeylTransports a ha mu w t t' := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  rw [relativeWeylConjugateSubgroupFunctor_mk] at hw
  have hconj : ConjugatesLevi (n : rationalPoints G) t.1 q :=
    (SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mpr hw
  let t' := conjugateFullIndex a ha mu t q hconj
  have ht' : WeylTransports a ha mu (QuotientGroup.mk n) t t' :=
    ⟨n, rfl, orbitConjugates_conjugateFullIndex a ha mu t q hconj⟩
  exact ⟨t', ⟨rfl, ht'⟩, fun y hy => hy.2.eq_of_same_parabolic ht' hM hy.1⟩

end Intrinsic

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
