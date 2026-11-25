import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLowerOrbit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacket
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport

/-! # Re-choosing the chamber of a lower Levi subgroup

In the proof of Waldspurger VI.3.1 (printed p.304) the induction hypothesis is applied to the
lower Levi `M' = M_{I'}` and its parabolic `M' ∩ s·P`. This parabolic is semistandard in `M'`
but in general not standard for the chamber `ν` of `M'`. Here we choose, inside `M'`, a new
generic chamber `ν'` for which the lower cocharacter is standard, and keep the same compact
subgroup with the same function `Ξ`.

* `StandardChamber`, `standardChamber`: a generic chamber in which a given cocharacter is
  standard, with `Finset` labels of the simple roots on which it vanishes.
* `lowerChamber`: such a chamber of `M'` for `sζ = n ζ n⁻¹`.
* `isIwasawaPair_lowerChamber`, `rationalXi_lowerChamber`, `isIwasawaPair_lowerCompact`,
  `rationalXi_lowerCompact`: the same compact subgroup (in particular `K ∩ M'`) is an Iwasawa
  compact for the new chamber, with the same `Ξ^{M'}`.
* `standardParabolicPoints_lowerChamber`, `standardLeviPoints_lowerChamber`: the standard
  parabolic and Levi of the new chamber are the lower groups `M' ∩ s·P_I` and `M' ∩ s·M_I`.
* `lowerChamberRepresentation`, `pullback_lowerChamberRepresentation`, `lowerDensityPackage_eq`:
  `sπ` as a representation of the new standard Levi; a lower density package is literally the
  density data of the target at `M'` for this representation.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz.LowerChamber

/-! ### A chamber in which a given cocharacter is standard -/

section Chamber

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] (j : T.toGrp ⟶ H)

/-- If every root negative on `lam` is negative on `ν'`, then `lam` is a standard cocharacter
of the chamber `ν'` for the simple roots of `ν'` on which it vanishes. -/
theorem isStandardCocharacter_zeroSimpleRoots {ν' lam : cocharacterLattice T}
    (href : ∀ b ∈ relativeRoots j, latticePairing T b lam < 0 → latticePairing T b ν' < 0) :
    IsStandardCocharacter j ν' (simpleRootFace j ν' lam) lam := by
  refine ⟨fun α hα => hα.1, fun α hα => hα.2, fun α hα hαJ => ?_⟩
  have hne : latticePairing T α lam ≠ 0 := fun h0 => hαJ ⟨hα, h0⟩
  have hpos : 0 < latticePairing T α ν' := hα.1.2
  rcases lt_or_gt_of_ne hne with hneg | hpos'
  · exact absurd (href α hα.1.1 hneg) (not_lt.2 hpos.le)
  · exact hpos'

/-- The `Finset` labels of `simpleRootFace`, for a chamber with finitely many simple roots. -/
def zeroLabels {ν' : cocharacterLattice T} (hfin : (simpleRelativeRoots j ν').Finite)
    (lam : cocharacterLattice T) : Finset (RationalPointFamily.SimpleRoot j ν') :=
  haveI : Finite (RationalPointFamily.SimpleRoot j ν') := hfin.to_subtype
  (Set.toFinite {a : RationalPointFamily.SimpleRoot j ν' |
    latticePairing T (a : characterLattice T) lam = 0}).toFinset

theorem rootSet_zeroLabels {ν' : cocharacterLattice T} (hfin : (simpleRelativeRoots j ν').Finite)
    (lam : cocharacterLattice T) :
    RationalPointFamily.rootSet j ν' (zeroLabels j hfin lam) = simpleRootFace j ν' lam := by
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, by simpa [zeroLabels] using ha⟩
  · rintro ⟨hα, h0⟩
    exact ⟨⟨α, hα⟩, by simpa [zeroLabels] using h0, rfl⟩

/-- **A chamber in which `lam` is standard.** A generic cocharacter `chamber` of `j`, refining
the signs of `lam` on the roots, and `Finset` labels of its simple roots for which `lam` is a
standard cocharacter. -/
structure StandardChamber (lam : cocharacterLattice T) where
  /-- The new generic cocharacter. -/
  chamber : cocharacterLattice T
  isGeneric : IsGenericCocharacter j chamber
  /-- The simple roots of `chamber` on which `lam` vanishes. -/
  labels : Finset (RationalPointFamily.SimpleRoot j chamber)
  rootSet_labels : RationalPointFamily.rootSet j chamber labels = simpleRootFace j chamber lam
  isStandard :
    IsStandardCocharacter j chamber (RationalPointFamily.rootSet j chamber labels) lam
  refines : ∀ b ∈ relativeRoots j,
    (0 < latticePairing T b lam → 0 < latticePairing T b chamber) ∧
      (latticePairing T b lam < 0 → latticePairing T b chamber < 0)

/-- Every cocharacter of a split torus is standard for some generic chamber
(`exists_genericCocharacter_refining`). -/
theorem nonempty_standardChamber [LocallyOfFiniteType H.X.hom] (hT : IsSplitTorus T.toGrp)
    (lam : cocharacterLattice T) : Nonempty (StandardChamber j lam) := by
  obtain ⟨mu, hgen, href⟩ := Langlands.Geometry.Building.exists_genericCocharacter_refining j hT lam
  have hfin : (simpleRelativeRoots j mu).Finite :=
    (hT.finite_relativeRoots j).subset fun _ hα => hα.1.1
  have hstd := isStandardCocharacter_zeroSimpleRoots j (fun b hb => (href b hb).2)
  exact ⟨{ chamber := mu, isGeneric := hgen, labels := zeroLabels j hfin lam
           rootSet_labels := rootSet_zeroLabels j hfin lam
           isStandard := by rw [rootSet_zeroLabels]; exact hstd
           refines := href }⟩

/-- A chosen chamber in which `lam` is standard. -/
def standardChamber [LocallyOfFiniteType H.X.hom] (hT : IsSplitTorus T.toGrp)
    (lam : cocharacterLattice T) : StandardChamber j lam :=
  Classical.choice (nonempty_standardChamber j hT lam)

end Chamber

/-! ### The lower Levi `M' = M_{I'}` and the conjugated cocharacter `sζ` -/

section Lower

open Langlands.Plancherel Langlands.Plancherel.DynamicOppositeStandardIntertwining
open RationalPointFamily WeakExpansion

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
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerChamberLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerChamberLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hi : IsMaximalSplitTorus i) (I' : Finset (SimpleRoot i ν))
  (ζ : cocharacterLattice T) (n : normalizerPoints i)

set_option hygiene false in
local notation "M'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "lam" => conjugatedCocharacter i ζ n

/-- **The chamber of `M'` for `sζ`.** A generic cocharacter `ν'` of the maximal split torus of
`M' = M_{I'}`, with labels `J''` of its simple roots, such that the conjugated cocharacter
`sζ = n ζ n⁻¹` is a standard cocharacter of `J''` for `ν'`. -/
def lowerChamber : StandardChamber iL lam :=
  standardChamber iL hi.isSplitSubtorus.1 lam

set_option hygiene false in
local notation "c" => lowerChamber hi I' ζ n

variable (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)

set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "hiL" => lowerTorus_isMaximalSplitTorus hi I'

/-! #### The same compact subgroup and the same `Ξ` -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hν in
/-- An Iwasawa compact of `M'` for the chamber `ν` is one for the chamber of `sζ`
(`IsIwasawaPair.rationalChangeMinimal`). -/
theorem isIwasawaPair_lowerChamber {K : Subgroup (rationalPoints M')}
    (hPK : IsIwasawaPair (standardParabolicPoints iL ν ∅) K) :
    IsIwasawaPair (standardParabolicPoints iL (c).chamber ∅) K :=
  IsIwasawaPair.rationalChangeMinimal hM' hiL (isGenericCocharacter_leviTorusHom hν)
    (c).isGeneric hPK

include hG hν in
/-- With the same compact subgroup, the chamber of `sζ` gives the same `Ξ^{M'}`
(`rationalXi_changeMinimal`). -/
theorem rationalXi_lowerChamber {K : Subgroup (rationalPoints M')}
    (hKo : IsOpen (K : Set (rationalPoints M'))) (hKc : IsCompact (K : Set (rationalPoints M')))
    (hPK : IsIwasawaPair (standardParabolicPoints iL ν ∅) K) (x : rationalPoints M') :
    rationalXi hKc (isIwasawaPair_lowerChamber hi I' ζ n hG hν hPK) x = rationalXi hKc hPK x :=
  rationalXi_changeMinimal hM' hiL (isGenericCocharacter_leviTorusHom hν) (c).isGeneric hKo hKc
    hPK (isIwasawaPair_lowerChamber hi I' ζ n hG hν hPK) x

/-- **The compact subgroup `K ∩ M'` of `M'`** as an open subgroup of `M'(F)`
(`leviSchemeCompact`). -/
def lowerCompact {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G))) :
    OpenSubgroup (rationalPoints M') where
  toSubgroup := leviSchemeCompact K i ν (rootSet i ν I')
  isOpen' := isOpen_leviSchemeCompact hKo

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
include hG hν in
/-- `M'(F) = (P_∅^{ν'}(F))(K ∩ M')` for the chamber `ν'` of `sζ`, from the Iwasawa
decomposition of `M_{I'}(F)` for `K ∩ M_{I'}(F)`. -/
theorem isIwasawaPair_lowerCompact {K : Subgroup (rationalPoints G)}
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (rootSet i ν I')))
      (K.subgroupOf (standardLeviPoints i ν (rootSet i ν I')))) :
    IsIwasawaPair (standardParabolicPoints iL (c).chamber ∅)
      (leviSchemeCompact K i ν (rootSet i ν I')) :=
  isIwasawaPair_lowerChamber hi I' ζ n hG hν
    (isIwasawaPair_leviSchemeCompact hG hi hν (rootSet_subset i ν I') hM)

/-- **`Ξ` is unchanged.** For `K ∩ M'` and the chamber of `sζ`, the spherical function of `M'`
is `Ξ^{M_{I'}}` of `K ∩ M_{I'}(F)` (`rationalXi_leviScheme`). -/
theorem rationalXi_lowerCompact {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (rootSet i ν I')))
      (K.subgroupOf (standardLeviPoints i ν (rootSet i ν I'))))
    (x : rationalPoints M') :
    rationalXi (isCompact_leviSchemeCompact hKc) (isIwasawaPair_lowerCompact hi I' ζ n hG hν hM) x =
      rationalLeviXi hKc hM (leviSchemePointsEquiv i ν (rootSet i ν I') x) := by
  rw [← rationalXi_leviScheme hG hi hν (rootSet_subset i ν I') hKo hKc hM x]
  exact rationalXi_lowerChamber hi I' ζ n hG hν (isOpen_leviSchemeCompact hKo)
    (isCompact_leviSchemeCompact hKc) _ x

/-! #### The lower groups are standard for the chamber of `sζ` -/

variable (I : Finset (SimpleRoot i ν)) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hν hζ in
/-- **The lower parabolic is standard.** The standard parabolic `P_{J''}` of `M'` for the chamber
of `sζ` is the lower parabolic `M' ∩ s·P_I` of Waldspurger V.1, as a subgroup of `M'(F)`. -/
theorem standardParabolicPoints_lowerChamber :
    standardParabolicPoints iL (c).chamber (rootSet iL (c).chamber (c).labels) =
      (lowerParabolic i ν (rootSet i ν I) (rootSet i ν I') n).rationalPoints :=
  (standardLeviPlancherelParabolic_eq hM' hiL (c).isGeneric (c).labels (c).isStandard).symm.trans
    (lowerCocharacter_points i ν (rootSet i ν I) (rootSet i ν I') hG hi hν (rootSet_subset i ν I)
      ζ hζ n).1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hν hζ in
/-- **The lower Levi is standard.** The standard Levi `M_{J''}` of `M'` for the chamber of `sζ`
is the lower Levi `M' ∩ s·M_I`, as a subgroup of `M'(F)`. -/
theorem standardLeviPoints_lowerChamber :
    standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels) =
      (lowerLevi i ν (rootSet i ν I) (rootSet i ν I') n).rationalPoints :=
  (congrArg (fun P : SubgroupFunctor M' => P.carrier (Over.mk (𝟙 _)))
    (Jacquet.standardLevi_eq_dynamic hM' hiL (c).isGeneric (c).isStandard).1).trans
    (lowerCocharacter_points i ν (rootSet i ν I) (rootSet i ν I') hG hi hν (rootSet_subset i ν I)
      ζ hζ n).2

/-! #### The conjugated representation on the standard Levi of the chamber of `sζ` -/

-- `M_I(F)` as a subtype of `G(F)`, written as in `standardLeviPlancherelWeight`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
-- The standard Levi `M_{J''}(F)` of `M'` for the chamber of `sζ`, in the same form.
set_option hygiene false in
local notation "𝐌'" => {x : rationalPoints M' //
  @Membership.mem (rationalPoints M') (Subgroup (rationalPoints M')) _
    (standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels)) x}

/-- `Z_{M'}(sζ)(F) = M_{J''}(F)`: the identification `standardLeviDynamicHomeomorph` of the
literal Levi `levi χ_s` of the lower cocharacter with the standard Levi of the chamber of `sζ`.
It is the identity on points of `M'(F)`. -/
abbrev lowerChamberLeviHomeomorph :=
  Langlands.Plancherel.standardLeviDynamicHomeomorph hM' hiL (c).isGeneric (c).labels
    (c).isStandard

variable (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

/-- **`sπ` on `M_{J''}(F)`.** The conjugated representation `sπ = π ∘ Int(n)⁻¹` of
`(s·M)(F) = Z_{M'}(sζ)(F)` (`lowerRepresentation`), viewed as a representation of the standard
Levi `M_{J''}(F)` of the chamber of `sζ`. -/
def lowerChamberRepresentation : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌') :=
  IrreducibleAdmissibleRep.pullback (lowerChamberLeviHomeomorph hi I' ζ n hG hν).symm
    (lowerRepresentation hG hi hν I I' hζ n hn π)

/-- The representation that the target's density hypotheses at `M'` use, `π' ∘ e` with
`e = lowerChamberLeviHomeomorph`, is literally `sπ`. -/
theorem pullback_lowerChamberRepresentation :
    SmoothRep.pullback (lowerChamberLeviHomeomorph hi I' ζ n hG hν)
        (lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π).obj =
      (lowerRepresentation hG hi hν I I' hζ n hn π).obj :=
  rfl

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

/-- **The lower density packages are the target's density hypotheses at `M'`.** A lower density
package `LowerDensityPackage` for `s` is, field by field, the data
`(K, hK, hPK, hOppK, p, q, D_forward, D_reverse, D, hirr, hreg)` that the source-normalized
target asks for at the ambient group `M'`, its maximal split torus, the chamber of `sζ`, the
labels `J''`, the cocharacter `sζ` and the representation `lowerChamberRepresentation`. -/
theorem lowerDensityPackage_eq :
    LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST =
      DynamicInducedOrbit.DensityPackage iL lam hRefl hCST hM'
        (SmoothRep.pullback (lowerChamberLeviHomeomorph hi I' ζ n hG hν)
          (lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π).obj) :=
  rfl

end Lower

end Langlands.HarishChandraSchwartz.LowerChamber
