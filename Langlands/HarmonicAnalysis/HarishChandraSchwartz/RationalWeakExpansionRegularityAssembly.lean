import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeightedCPoleCancellation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionJointDomain

/-! # Corollary V.2.3 from three named inputs

See the paired Markdown. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily

universe u uV

section Weighted

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance regularityInputsAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance regularityInputsLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance regularityInputsLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance regularityInputsLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance regularityInputsPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph eM ν₀
set_option hygiene false in
local notation "Φu" => standardLeviUnitaryCharacterHomeomorph I

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "Wₛ" => ProductInducedCompactPicture (decomposition χs)
  (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM) (SmoothRep.pullback (eₛ).symm π.obj)
set_option hygiene false in
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "A₀" => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN
set_option hygiene false in
local notation "Ω" => Φ ⁻¹' interior D₀
set_option hygiene false in
local notation "A" => fun z : (Ω : Set (unramifiedCharacters ν₀)) =>
  A₀ ⟨Φ z.val, interior_subset z.property⟩
set_option hygiene false in
local notation "Extension" => WeightedCExtension hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
  π PG PM hN


variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ M₀) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [MeasurableSpace (𝐌 ⧸ CM)] (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]

/-- **Rational continuation with unitary pole presentation** (input for Waldspurger V.2.3,
printed p.294, from IV.1 (12) and V.2.1). On the Borel quotient `M_I(F)/C_M` with Haar measure
`μ`: if `π` is square integrable modulo `C_M` and `K` is special, the weighted family
`c̃_{P'|P}(s, ·)`, transported to the scheme characters of `M_I` on `Ω = Φ⁻¹(interior D₀)`, has a
rational continuation (`RationalOperatorContinuationData`: one polynomial numerator and one
regular denominator nonvanishing on all of `Ω`) together with a pole presentation
(`RationalOperatorPolePresentation`) of that continuation: its unitary poles lie on finitely many
unit-circle basis-coordinate hyperplanes. -/
def WeightedCContinuationPolesStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  IsSpecialVertexCompact ν hi K →
  ∃ p : RationalOperatorContinuationData Ω A,
    Nonempty (RationalOperatorPolePresentation M₀ p.denominator p.numerator)

/-- **Unitary bound of the continued weighted family** (input for Waldspurger V.2.3, from Lemma
V.2.2, printed pp.293–294). On the Borel quotient `M_I(F)/C_M` with Haar measure `μ`: if `π` is
square integrable modulo `C_M`, `K` is special and the interior of `D₀` is nonempty, then there
is a linear equivalence `e` of the lower compact picture with a complex normed space such that
every rational continuation `N/b` of the transported weighted family on `Ω` satisfies the cleared
unitary bound: for each vector `v` there is `C ≥ 0` with `‖e (N(z) v)‖ ≤ C ‖b(z)‖` at every
unitary `z` (`HasClearedUnitaryBound`). -/
def WeightedCUnitaryBoundStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  IsSpecialVertexCompact ν hi K →
  (interior D₀).Nonempty →
  ∃ (E : Type (max u uV)) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (e : Wₛ ≃ₗ[ℂ] E),
    ∀ p : RationalOperatorContinuationData Ω A,
      HasClearedUnitaryBound M₀ (fun z => e.toLinearMap.comp (p.numerator z)) p.denominator

/-! ### Corollary V.2.3 from the three inputs -/

variable (Rep : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PMf : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (Rep.normalizer s) (Rep.levi_le s) π hRefl hCST)

set_option linter.overlappingInstances false in
/-- **Reduction of Corollary V.2.3 to three inputs.** For every Weyl index `s`: the joint
convergence interior is nonempty (`CDomainInteriorNonemptyStatement`), the weighted family has a
rational continuation with a unitary pole presentation (`WeightedCContinuationPolesStatement`),
and its continuations satisfy the cleared unitary bound (`WeightedCUnitaryBoundStatement`). Then
the regularity target `WeightedCRegularityBorelStatement` holds, for the same data and the same
Borel instance. -/
def WeightedCRegularityFromInputsStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  (∀ s, CDomainInteriorNonemptyStatement hG hi hν I I' hζ hζ' (Rep.normalizer s)
    (Rep.levi_le s) hK sc hs π mu) →
  (∀ s (hN' : CommonCompactNormalization hG hi hν I I' hζ (Rep.normalizer s) (Rep.levi_le s) K
      hRefl hCST π PG (PMf s)),
    WeightedCContinuationPolesStatement hG hi hν I I' hζ hζ' (Rep.normalizer s) (Rep.levi_le s)
      K hK hRefl hCST hPK π PG (PMf s) hN' sc hs mu) →
  (∀ s (hN' : CommonCompactNormalization hG hi hν I I' hζ (Rep.normalizer s) (Rep.levi_le s) K
      hRefl hCST π PG (PMf s)),
    WeightedCUnitaryBoundStatement hG hi hν I I' hζ hζ' (Rep.normalizer s) (Rep.levi_le s)
      K hK hRefl hCST hPK π PG (PMf s) hN' sc hs mu) →
  WeightedCRegularityBorelStatement hG hi hν I I' hζ hζ' hK hPK sc hs π mu hRefl hCST PG Rep PMf

set_option linter.overlappingInstances false in
/-- Proof of `WeightedCRegularityFromInputsStatement`: for each `s`, the nonempty interior of
`D₀` comes from `cWeightedDomain_interior_nonempty_of_cDomain`, and `weightedCExtensionFromPoles`
turns the continuation, its pole presentation and the bound into a `WeightedCExtension`. -/
theorem weightedCRegularityFromInputs [BorelSpace (𝐌 ⧸ CM)] :
    WeightedCRegularityFromInputsStatement hG hi hν I I' hζ hζ' K hK hRefl hCST hPK π PG sc hs mu
      Rep PMf := by
  intro hD hP hB hsq _ hKs hN s
  have hint := cWeightedDomain_interior_nonempty_of_cDomain hG hi hν I I' hζ hζ'
    (Rep.normalizer s) (Rep.levi_le s) hK sc hs π mu hRefl hCST PG (PMf s) (hD s) hsq hKs hPK
  obtain ⟨p, hq⟩ := hP s (hN s) hsq hKs
  obtain ⟨E, _, _, e, hb⟩ := hB s (hN s) hsq hKs hint
  exact weightedCExtensionFromPoles hG hi hν I I' hζ hζ' (Rep.normalizer s) (Rep.levi_le s) K hK
    hRefl hCST hPK π PG (PMf s) (hN s) e hint p hq (hb p)

end Weighted

end Langlands.HarishChandraSchwartz.WeakExpansion
