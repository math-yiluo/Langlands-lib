import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeightedCDomain
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionDensityNonzero

/-! # Nonempty joint convergence interior of the c-family

The published `WeightedCExtension` (module `RationalWeakExpansionTargets`) contains the
nonemptiness of the interior of the domain `cWeightedDomain` of the weighted c-family
`c̃_{P'|P}(s, ·)`. The published `cWeightedDomain_interior_nonempty_iff` reduces it to two inputs:
the interior of the joint convergence domain `cDomain` is nonempty, and the lower package's
canonical scalar is nonzero. The second input is the published
`lowerDensityCanonicalScalarNonzero`.

This module states the first input, `CDomainInteriorNonemptyStatement` (not proved here), and
proves `cWeightedDomain_interior_nonempty_of_cDomain`: under square integrability, the statement
gives the nonempty interior of `cWeightedDomain` for all density packages. -/

noncomputable section

set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance jointDomainAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance jointDomainLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance jointDomainLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance jointDomainLeviFiniteType (J : Set (characterLattice T)) :
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
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

-- `M_I(F)` as a subtype of `G(F)`, written as in `RationalWeakExpansionTargets`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]

/-- **Nonempty joint convergence interior** (Waldspurger IV.1 and V.1, printed pp.278 and 288):
for the Borel quotient `M_I(F)/C_M` with Haar measure `μ`, if `π` is square integrable modulo
`C_M`, `K` is the special maximal compact subgroup, and `K` is an Iwasawa complement of the
standard minimal parabolic, then for the normalizer lift `n` with `s·M ⊆ M'` the set of unramified
characters `z` of `M_I` at which both integrals of the c-family converge, `J_{P_s|s·P}` on
`ⁿ(π ⊗ z)` and `J_{P̃_s|s·P}` on `ⁿ(π ⊗ z)ˇ` (`cDomain`), has nonempty interior. -/
def CDomainInteriorNonemptyStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  IsSpecialVertexCompact ν hi K →
  IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)) →
  (interior (cDomain hG hi hν I I' hζ hζ' n hn K hKc π.obj)).Nonempty

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

/-- **The weighted domain has nonempty interior once the joint convergence domain has.** Under
`CDomainInteriorNonemptyStatement`, if `π` is square integrable modulo `C_M`, `K` is special and an
Iwasawa complement of the standard minimal parabolic, then for all density packages `PG` and `PM`
the interior of `cWeightedDomain` is nonempty: by `cWeightedDomain_interior_nonempty_iff`, with the
nonvanishing of the lower canonical scalar from `lowerDensityCanonicalScalarNonzero`. -/
theorem cWeightedDomain_interior_nonempty_of_cDomain [BorelSpace (𝐌 ⧸ CM)]
    (h : CDomainInteriorNonemptyStatement hG hi hν I I' hζ hζ' n hn hKc sc hs π mu)
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
    (hK : IsSpecialVertexCompact ν hi K)
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G))) :
    (interior (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM)).Nonempty :=
  (cWeightedDomain_interior_nonempty_iff hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM).2
    ⟨h hsq hK hPK,
      lowerDensityCanonicalScalarNonzero hG hi hν I I' hζ n hn sc hs π mu hRefl hCST PM hsq⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
