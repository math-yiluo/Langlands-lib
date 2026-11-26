import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierReconstruction

/-! # Waldspurger VIII.1.1: surjectivity of the actual synthesis `κ`

Waldspurger (2003), Théorème VIII.1.1, printed p. 320. The targets are Prop-valued
definitions; the module proves only that VIII.1 (1) and (2) together give
surjectivity. -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion

open GlobalSynthesis

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

local instance surjectivityCompactOpen {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance surjectivityParabolicLC {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

section FixedData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K0 hK0 hKc hPK rho)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K0)
  (hQ : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K0)

set_option hygiene false in
set_option quotPrecheck false in
local notation "κ" => invariantSynthesis hG a ha mu d C.presentation hindex Q K0 hK0 C hi
  semistandardSpectralFiberFiniteness hKc hPK rho hsynth hnu hspecial hd hQ

/-- **Théorème VIII.1.1** for one choice of the construction data: the actual
synthesis `κ : C^∞(Θ)_inv → C(G)` is surjective. The only construction inputs are
those of `κ`, including the VI.3.1 Schwartz membership witness `hsynth`; no
surjectivity, reconstruction or Fourier finiteness is an input. -/
def SynthesisSurjectivityStatement : Prop :=
  Function.Surjective κ

omit [∀ t, (mu t).IsInvInvariant] in
theorem synthesisSurjectivityStatement_iff_range :
    SynthesisSurjectivityStatement hG hi hnu hKc hPK rho a ha mu d C hindex Q K0 hK0 hsynth hspecial
        hd hQ ↔
      LinearMap.range κ = ⊤ :=
  LinearMap.range_eq_top.symm

section Fourier

variable {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

/-- VIII.1 (1) and (2) together give VIII.1.1: each Schwartz function is the value of
`κ` at its own invariant Fourier lift. No inverse identity is used. -/
theorem synthesisSurjectivity_of_fourierInversion
    (h : FourierInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
      hK0 hsynth hspecial hd hQ) :
    SynthesisSurjectivityStatement hG hi hnu hKc hPK rho a ha mu d C hindex Q K0 hK0 hsynth hspecial
      hd hQ :=
  surjective_of_fourierInversion hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
    hsynth hspecial hd hQ h

/-- The same implication from the separate support and reconstruction targets. -/
theorem synthesisSurjectivity_of_lift_of_reconstruction
    (hlift : FourierInvariantLiftStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C)
    (hrec : SynthesisReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex
      Q K0 hK0 hsynth hspecial hd hQ) :
    SynthesisSurjectivityStatement hG hi hnu hKc hPK rho a ha mu d C hindex Q K0 hK0 hsynth hspecial
      hd hQ :=
  synthesisSurjectivity_of_fourierInversion hG hi hnu hKc hPK rho a ha mu d C hindex Q K0 hK0
    hsynth hspecial hd hQ hsw hdelta hT
    ((fourierInversionStatement_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
      hK0 hsynth hspecial hd hQ).mpr ⟨hlift, hrec⟩)

end Fourier

end FixedData

/-- Local VIII.1.1 for one group: for all source data with the I.1 normalizations (one
source special compact `K` serving as the Schwartz compact, as `Kbase` and `K0` of `κ`
and as the compact of every compact picture and scalar datum, a source height `rho`, that
is a closed matrix embedding with `K` in its integral subgroup, and the I.1
split-central quotient Haar measures), the actual synthesis `κ` onto the source
Harish-Chandra Schwartz space is surjective. -/
def RationalLocalSynthesisSurjectivityStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho)
    (_hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
    [∀ t, IsAffine (T t).X.left]
    (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
    (ha : ∀ t, IsSplitComponent (a t))
    [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
    [∀ t, (rationalPoints.map (a t)).range.Normal]
    [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
    [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
    (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
    (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
    (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
    (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      OrbitPacketData (C.presentation theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
          (mu theta.1) theta.2))
    (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K)
    (hQ : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hsynth hspecial
      hd hQ

/-- All-field, all-group closure of local VIII.1.1. -/
def RationalSynthesisSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    RationalLocalSynthesisSurjectivityStatement.{u, uV} G

end Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion
