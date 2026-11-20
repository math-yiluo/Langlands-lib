import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitConjugation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationStabilizer
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences

/-! # Actual orbit and representative transport for semistandard wave-packet sums -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

universe u uV v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

open Association

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}

/-- A point conjugacy of the literal Levis induces the all-test conjugacy. -/
theorem conjugatesLevi_of_map_levi_eq {p q : SemistandardSpectralIndex i}
    {g : rationalPoints G} (hg : (levi p).map (MulAut.conj g).toMonoidHom = levi q) :
    ConjugatesLevi g p q := by
  let m := chosenLeviModel p
  let n := chosenLeviModel q
  let e := G.innerIso g
  let j := m.inclusion ≫ e.hom
  have hm : SubgroupFunctor.range j = p.levi.comap e.inv := by
    dsimp only [j]
    rw [SubgroupFunctor.range_comp_iso, m.represents.2]
  have hpts : (SubgroupFunctor.range j).rationalPoints =
      (SubgroupFunctor.range n.inclusion).rationalPoints := by
    rw [hm, n.represents.2, SubgroupFunctor.rationalPoints_comap_innerIso_inv]
    exact hg
  have := m.reductive.smooth
  have := m.reductive.isAffineHom
  have := m.reductive.connectedSpace
  have := n.reductive.smooth
  have := n.reductive.isAffineHom
  have := n.reductive.connectedSpace
  have heq : SubgroupFunctor.range j = SubgroupFunctor.range n.inclusion :=
    le_antisymm (SubgroupFunctor.range_le_of_localField_points n.closed hpts.le)
      (SubgroupFunctor.range_le_of_localField_points (m.closed.comp_iso e) hpts.ge)
  exact (SubgroupFunctor.eq_comap_iso_iff e).mpr
    (hm.symm.trans (heq.trans n.represents.2))

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "model" => fun p => chosenLeviModel p
set_option hygiene false in
local notation "center" => fun p => (model p).splitCenter (a p)
set_option hygiene false in
local notation "central" => fun p => (model p).splitCenter_le_center (a p) (ha p)
set_option hygiene false in
local notation "Point" => GlobalForm.OrbitPoint a ha mu
set_option hygiene false in
local notation "base" t:max => orbitRepresentative (model t.1) (a t.1) (ha t.1) (mu t.1) t.2
set_option hygiene false in
local notation "sqBase" t:max =>
  orbitRepresentative_isSquareIntegrable (model t.1) (a t.1) (ha t.1) (mu t.1) t.2

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
/-- An actual point of the orbit integral has exactly that full index's orbit class. -/
theorem orbitPoint_mk (t : Theta) (omega : Point t) :
    (Quotient.mk _ omega.val : OrbitClass (model t.1) (a t.1) (ha t.1) (mu t.1)) = t.2 := by
  exact (Quotient.sound omega.property).trans
    (mk_discreteSeriesClass_orbitRepresentative (model t.1) (a t.1) (ha t.1) (mu t.1) t.2)

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
/-- Membership in the constituent set is equality of the actual orbit classes. -/
theorem mem_orbitConstituents_iff (t : Theta)
    (omega : DiscreteSeriesClass.{u, uV} (center t.1) (central t.1) (mu t.1)) :
    omega.val ∈ orbitConstituents a ha mu t ↔
      (Quotient.mk _ omega : OrbitClass (model t.1) (a t.1) (ha t.1) (mu t.1)) = t.2 := by
  constructor
  · rintro ⟨omega', h, hOrbit⟩
    exact (congrArg (Quotient.mk _) (Subtype.ext h)).symm.trans hOrbit
  · exact fun h => ⟨omega, rfl, h⟩

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
/-- Regard a discrete series with the given orbit class as a point of that orbit. -/
def orbitPointOfClass (t : Theta)
    (omega : DiscreteSeriesClass.{u, uV} (center t.1) (central t.1) (mu t.1))
    (h : (Quotient.mk _ omega : OrbitClass (model t.1) (a t.1) (ha t.1) (mu t.1)) = t.2) :
    Point t :=
  ⟨omega, Quotient.exact (h.trans
    (mk_discreteSeriesClass_orbitRepresentative (model t.1) (a t.1) (ha t.1) (mu t.1) t.2).symm)⟩

variable (t : Theta) (q : SemistandardSpectralIndex i)
  {g : rationalPoints G} (hc : ConjugatesLevi g t.1 q)

set_option hygiene false in
local notation "target" => conjugateFullIndex a ha mu t q hc
set_option hygiene false in
local notation "pushClass" =>
  conjugateDiscreteSeriesClass hc (model t.1) (model q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
set_option hygiene false in
local notation "pushOrbit" =>
  conjugateOrbit hc (model t.1) (model q) (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
set_option hygiene false in
local notation "targetBase" => orbitRepresentative (model q) (a q) (ha q) (mu q) (pushOrbit t.2)
set_option hygiene false in
local notation "sqTargetBase" =>
  orbitRepresentative_isSquareIntegrable (model q) (a q) (ha q) (mu q) (pushOrbit t.2)

/-- The source point transported to the orbit used in the target coefficient pairing. -/
def conjugateOrbitPoint (omega : Point t) : Point target :=
  orbitPointOfClass a ha mu target (pushClass omega.val)
    (congrArg pushOrbit (orbitPoint_mk a ha mu t omega))

/-- The actual pullback of the inducing object, in the transported orbit. -/
def conjugateOrbitRepresentative (A : UnitaryOrbitRepresentative (model t.1).normCharacters (base t)) :
    UnitaryOrbitRepresentative (model q).normCharacters targetBase := by
  let omega := unitaryOrbitRepresentativeDiscreteSeriesOrbit (model t.1).normCharacters
    (base t) (center t.1) (central t.1) (mu t.1) (sqBase t) A
  let omega' := conjugateOrbitPoint a ha mu t q hc omega
  let B := IrreducibleAdmissibleRep.pullback (leviPointConjugation hc).symm A.val
  have hB : IsSquareIntegrableModCentralSubgroup (center q) (central q) B.obj.representation (mu q) :=
    omega'.val.property
  exact orbitRepresentativeMember (model q) (a q) (ha q) (mu q) (pushOrbit t.2) B hB
    (orbitPoint_mk a ha mu target omega')

@[simp]
theorem conjugateOrbitRepresentative_val
    (A : UnitaryOrbitRepresentative (model t.1).normCharacters (base t)) :
    (conjugateOrbitRepresentative a ha mu t q hc A).val =
      IrreducibleAdmissibleRep.pullback (leviPointConjugation hc).symm A.val := rfl

/-- The representative formula for orbit-point transport. -/
theorem conjugateOrbitPoint_representative
    (A : UnitaryOrbitRepresentative (model t.1).normCharacters (base t)) :
    conjugateOrbitPoint a ha mu t q hc
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit (model t.1).normCharacters
        (base t) (center t.1) (central t.1) (mu t.1) (sqBase t) A) =
      unitaryOrbitRepresentativeDiscreteSeriesOrbit (model q).normCharacters
        targetBase (center q) (central q) (mu q) sqTargetBase
        (conjugateOrbitRepresentative a ha mu t q hc A) :=
  Subtype.ext (Subtype.ext rfl)

private theorem pullback_symm_pullback {H L : Type u} [Group H] [Group L]
    [TopologicalSpace H] [TopologicalSpace L] (e : L ≃ₜ* H)
    (w : SmoothDualClass.{0, u, uV} (k := ℂ) (G := H)) :
    SmoothDualClass.pullback e.symm (SmoothDualClass.pullback e w) = w := by
  induction w using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.pullbackSymmIso e A.obj)⟩

/-- A target constituent belongs to the transported orbit exactly when its inverse
conjugate belongs to the source orbit. -/
theorem mem_conjugateFullIndex_iff
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi q)) :
    omega ∈ orbitConstituents a ha mu target ↔
      SmoothDualClass.pullback (leviPointConjugation hc) omega ∈ orbitConstituents a ha mu t := by
  obtain ⟨_, h⟩ := orbitConjugates_conjugateFullIndex a ha mu t q hc
  change SmoothDualClass.pullback (leviPointConjugation hc).symm '' orbitConstituents a ha mu t =
    orbitConstituents a ha mu target at h
  rw [← h]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show SmoothDualClass.pullback (leviPointConjugation hc)
        (SmoothDualClass.pullback (leviPointConjugation hc).symm w) = w from
      pullback_symm_pullback (leviPointConjugation hc).symm w]
    exact hw
  · exact fun hw => ⟨_, hw, pullback_symm_pullback (leviPointConjugation hc) omega⟩

omit hc in
/-- Every lift of a Weyl element transporting the orbit gives that same full target index. -/
theorem conjugateFullIndex_eq_of_weylTransports (t' : Theta)
    (hM : torusCentralizer i ≤ t.1.levi) (n : normalizerPoints i)
    (hn : ConjugatesLevi (n : rationalPoints G) t.1 t'.1)
    (h : WeylTransports a ha mu (QuotientGroup.mk n) t t') :
    conjugateFullIndex a ha mu t t'.1 hn = t' :=
  WeylTransports.eq_of_same_parabolic
    ⟨n, rfl, orbitConjugates_conjugateFullIndex a ha mu t t'.1 hn⟩ h hM rfl

section Quotient

variable (t' : Theta) (hM : torusCentralizer i ≤ t.1.levi)

set_option hygiene false in
local notation "WEqual" => SemistandardWeylConjugacyQuotient i t.1.toLevi t'.1.toLevi hM
set_option hygiene false in
local notation "WIncl" => SemistandardWeylTransporterQuotient i t.1.toLevi t'.1.toLevi hM

omit [∀ p, (mu p).IsHaarMeasure] in
/-- The inclusion of the equality transporter preserves the left target-Weyl classes. -/
def conjugacyQuotientToTransporter : WEqual → WIncl :=
  Quotient.map (fun w => ⟨w.val,
    semistandardWeylConjugacySet_subset_transporter i t.1.toLevi t'.1.toLevi hM w.property⟩)
    (fun _ _ h => h)

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
theorem conjugacyQuotientToTransporter_injective :
    Function.Injective (conjugacyQuotientToTransporter a ha mu t t' hM) := by
  intro w v
  induction w using Quotient.inductionOn with
  | h w =>
    induction v using Quotient.inductionOn with
    | h v =>
      intro h
      let lift (s : semistandardWeylConjugacySet i t.1.toLevi t'.1.toLevi hM) :
          semistandardWeylTransporterSet i t.1.toLevi t'.1.toLevi hM :=
        ⟨s.val, semistandardWeylConjugacySet_subset_transporter i t.1.toLevi t'.1.toLevi hM
          s.property⟩
      have h' : Quotient.mk (semistandardWeylTransporterRel i t.1.toLevi t'.1.toLevi hM)
          (lift w) = Quotient.mk _ (lift v) := h
      have hrel : (semistandardWeylTransporterRel i t.1.toLevi t'.1.toLevi hM).r
          (lift w) (lift v) := Quotient.exact h'
      exact Quotient.sound hrel

/-- The orbit filter `sO = O'` on the actual Weyl equality quotient. -/
abbrev OrbitWeylTransporters :=
  {w : WEqual //
    quotientWeylTransports a ha mu t t' hM (conjugacyQuotientToTransporter a ha mu t t' hM w)}

/-- Both source quotient conventions count the same classes under the orbit filter,
which already forces equality of the transported Levi. -/
def orbitWeylTransportersEquiv :
    OrbitWeylTransporters a ha mu t t' hM ≃
      {w : WIncl // quotientWeylTransports a ha mu t t' hM w} := by
  let f : OrbitWeylTransporters a ha mu t t' hM →
      {w : WIncl // quotientWeylTransports a ha mu t t' hM w} :=
    fun w => ⟨conjugacyQuotientToTransporter a ha mu t t' hM w.val, w.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro w v h
    exact Subtype.ext (conjugacyQuotientToTransporter_injective a ha mu t t' hM
      (congrArg Subtype.val h))
  · rintro ⟨w, hw⟩
    induction w using Quotient.inductionOn with
    | h w =>
      have hs := (quotientWeylTransports_mk a ha mu t t' hM w).mp hw
      let v : semistandardWeylConjugacySet i t.1.toLevi t'.1.toLevi hM :=
        ⟨w.val, hs.levi_eq hM⟩
      exact ⟨⟨Quotient.mk _ v, hw⟩, Subtype.ext rfl⟩

variable [Finite (relativeWeylGroup i)] {A : Type v} [AddCommMonoid A]

/-- The finite sum counts each retained left Weyl class once. -/
def orbitWeylSum (term : OrbitWeylTransporters a ha mu t t' hM → A) : A :=
  letI := Fintype.ofFinite (OrbitWeylTransporters a ha mu t t' hM)
  ∑ w, term w

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
/-- Reindexing on the original inclusion quotient gives the identical sum. -/
theorem orbitWeylSum_eq_transporterSum (term : OrbitWeylTransporters a ha mu t t' hM → A) :
    orbitWeylSum a ha mu t t' hM term =
      letI := Fintype.ofFinite {w : WIncl // quotientWeylTransports a ha mu t t' hM w}
      ∑ w, term ((orbitWeylTransportersEquiv a ha mu t t' hM).symm w) := by
  classical
  let _ := Fintype.ofFinite (OrbitWeylTransporters a ha mu t t' hM)
  let _ := Fintype.ofFinite {w : WIncl // quotientWeylTransports a ha mu t t' hM w}
  exact Fintype.sum_equiv (orbitWeylTransportersEquiv a ha mu t t' hM) _ _
    (fun w => by rw [Equiv.symm_apply_apply])

omit [∀ p, BorelSpace (levi p ⧸ center p)] in
theorem orbitWeylSum_of_isEmpty [IsEmpty (OrbitWeylTransporters a ha mu t t' hM)]
    (term : OrbitWeylTransporters a ha mu t t' hM → A) :
    orbitWeylSum a ha mu t t' hM term = 0 := by
  simp [orbitWeylSum]

end Quotient

end Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing
