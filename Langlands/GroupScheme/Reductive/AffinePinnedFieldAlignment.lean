import Langlands.GroupScheme.Reductive.AffinePinnedBorelNormalization
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # Actual coordinate root alignment on a field test -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

local instance (M : AffinePinnedModel.{u}) : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

local instance (M : AffinePinnedModel.{u}) : Smooth M.group.X.hom :=
  M.reductive.smooth

/-- The actual canonical Borel represents the model's normalized dynamic
parabolic after arbitrary base change. -/
theorem borelInclusionOver_represents (M : AffinePinnedModel.{u})
    {T : Scheme.{u}} (f : T ⟶ M.base) :
    (Dynamic.parabolic (M.cocharacterOver f)).IsRepresentedBy
      (M.borelInclusionOver f) := by
  have h := (Dynamic.Affine.isRepresentedBy_parabolicHom
    (BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis)).baseChange f
  rw [← Dynamic.parabolic_baseChange, ← M.cocharacterOver_eq_baseChange f] at h
  exact h

/-- A canonical-Borel square identifies the transported actual dynamic
parabolics. -/
theorem PreservesBorel.parabolic_eq
    {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base} {e : Comparison f g}
    (he : PreservesBorel e) :
    Dynamic.parabolic (M.cocharacterOver f ≫ e.hom) =
      Dynamic.parabolic (N.cocharacterOver g) := by
  obtain ⟨β, hβ⟩ := he
  have h := (Dynamic.range_eq_parabolic_comp_iso_iff
    (M.borelInclusionOver f) (M.cocharacterOver f) e).mpr
      (M.borelInclusionOver_represents f).2
  rw [hβ, SubgroupFunctor.range_iso_comp,
    (N.borelInclusionOver_represents g).2] at h
  exact h.symm

local instance (M : AffinePinnedModel.{u}) (k : Type u)
    [CommRing k] [Algebra M.ring k] :
    IsAffineHom (M.groupOver (algebraBaseMap M.ring k)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring k)))

variable (M N : AffinePinnedModel.{u}) (k : Type u) [Field k]
  [Algebra M.ring k] [Algebra N.ring k]
  (e : Comparison (algebraBaseMap M.ring k) (algebraBaseMap N.ring k))
  (τ : splitTorus (Spec (CommRingCat.of k)) M.coordinates ≅
    splitTorus (Spec (CommRingCat.of k)) N.coordinates)
  (hτ : M.inclusionOver (algebraBaseMap M.ring k) ≫ e.hom =
    τ.hom ≫ N.inclusionOver (algebraBaseMap N.ring k))

private def fieldRealizedEquiv :
    RootPairing.Equiv (CoordinateRootDatum.fieldRealization k N.rootDatum)
      (CoordinateRootDatum.fieldRealization k M.rootDatum) :=
  rootDatumEquivOfTorusCompatibleIso
    (M.reductive.isConnectedReductive_algebraMap k)
    (N.reductive.isConnectedReductive_algebraMap k)
    (isSplitTorus_splitTorus M.coordinates) (isSplitTorus_splitTorus N.coordinates)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      M.coordinates M.group M.inclusion M.maximal k)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      N.coordinates N.group N.inclusion N.maximal k)
    e (CommGroupScheme.isoOfGroupIso τ) hτ
    (M.fibrewiseRootDatum.field k) (N.fibrewiseRootDatum.field k)

/-- The full coordinate root-datum equivalence induced by the supplied actual
torus-compatible comparison on a field test. -/
def fieldCoordinateEquiv : RootPairing.Equiv N.rootDatum M.rootDatum :=
  CoordinateRootDatum.equivOfFieldRealizationEquiv k N.rootDatum M.rootDatum
    (fieldRealizedEquiv M N k e τ hτ)

/-- The coordinate weight map is the pullback by the actual supplied torus
isomorphism, on the entire character lattice. -/
theorem fieldCoordinateEquiv_character (m : N.coordinates → ℤ) :
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        ((fieldCoordinateEquiv M N k e τ hτ).weightMap m) =
      (CommGroupScheme.isoOfGroupIso τ).hom ≫
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) N.coordinates m := by
  have h := rootDatumEquivOfTorusCompatibleIso_weightMap
    (M.reductive.isConnectedReductive_algebraMap k)
    (N.reductive.isConnectedReductive_algebraMap k)
    (isSplitTorus_splitTorus M.coordinates) (isSplitTorus_splitTorus N.coordinates)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      M.coordinates M.group M.inclusion M.maximal k)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      N.coordinates N.group N.inclusion N.maximal k)
    e (CommGroupScheme.isoOfGroupIso τ) hτ
    (M.fibrewiseRootDatum.field k) (N.fibrewiseRootDatum.field k)
    (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) N.coordinates m)
  change (fieldRealizedEquiv M N k e τ hτ).weightMap _ = _ at h
  have hreal :
      (CoordinateRootDatum.fieldRealizationEquiv k M.rootDatum).weightMap
          ((fieldCoordinateEquiv M N k e τ hτ).weightMap m) =
        (fieldRealizedEquiv M N k e τ hτ).weightMap
          ((CoordinateRootDatum.fieldRealizationEquiv k N.rootDatum).weightMap m) := by
    change (CoordinateRootDatum.fieldRealizationEquiv k M.rootDatum).weightEquiv
        ((CoordinateRootDatum.fieldRealizationEquiv k M.rootDatum).weightEquiv.symm
          ((fieldRealizedEquiv M N k e τ hτ).weightMap
            ((CoordinateRootDatum.fieldRealizationEquiv k N.rootDatum).weightMap m))) = _
    exact LinearEquiv.apply_symm_apply _ _
  simp only [CoordinateRootDatum.fieldRealizationEquiv_weightMap] at hreal
  exact hreal.trans h

/-- A canonical-Borel square makes the prescribed coordinate equivalence
preserve positivity. -/
theorem fieldCoordinateEquiv_isPos (he : PreservesBorel e) (a : N.rootIndex) :
    M.basis.IsPos ((fieldCoordinateEquiv M N k e τ hτ).indexEquiv a) ↔
      N.basis.IsPos a := by
  let : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced
  let : N.rootDatum.IsReduced := N.fibrewiseRootDatum.isReduced
  let r := fieldCoordinateEquiv M N k e τ hτ
  let nuSource := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) M.coordinates
    (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis)
  let nuTarget := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) N.coordinates
    (BasedBorelExponent.positiveCorootSum N.rootDatum N.basis)
  let t : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) N.coordinates :=
    CommGroupScheme.isoOfGroupIso τ
  have hpar := he.parabolic_eq
  change Dynamic.parabolic ((CommGroupScheme.groupHom nuSource ≫
    M.inclusionOver (algebraBaseMap M.ring k)) ≫ e.hom) =
    Dynamic.parabolic (CommGroupScheme.groupHom nuTarget ≫
      N.inclusionOver (algebraBaseMap N.ring k)) at hpar
  rw [Category.assoc, hτ, ← Category.assoc] at hpar
  change Dynamic.parabolic (CommGroupScheme.groupHom (nuSource ≫ t.hom) ≫
    N.inclusionOver (algebraBaseMap N.ring k)) =
    Dynamic.parabolic (CommGroupScheme.groupHom nuTarget ≫
      N.inclusionOver (algebraBaseMap N.ring k)) at hpar
  have hmax := (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    N.coordinates N.group N.inclusion N.maximal k).isMaximalSplitTorus
      (isSplitTorus_splitTorus N.coordinates)
  have hforward := (relativeRootSignInclusions k
    (N.groupOver (algebraBaseMap N.ring k))
    (N.reductive.isConnectedReductive_algebraMap k)
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) N.coordinates)
    (N.inclusionOver (algebraBaseMap N.ring k)) hmax (nuSource ≫ t.hom) nuTarget).1.mp
      (le_of_eq hpar)
  have hback := (relativeRootSignInclusions k
    (N.groupOver (algebraBaseMap N.ring k))
    (N.reductive.isConnectedReductive_algebraMap k)
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) N.coordinates)
    (N.inclusionOver (algebraBaseMap N.ring k)) hmax nuTarget (nuSource ≫ t.hom)).1.mp
      (le_of_eq hpar.symm)
  let α := splitTorus.exponentCharacter (Spec (CommRingCat.of k))
    N.coordinates (N.rootDatum.root a)
  have hα : α ∈ relativeRoots (N.inclusionOver (algebraBaseMap N.ring k)) := by
    rw [relativeRoots_eq_roots]
    exact (N.fibrewiseRootDatum.mem_roots_iff k _).mpr (Set.mem_range_self a)
  have hnuSource : latticePairing
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) N.coordinates)
      α (nuSource ≫ t.hom) = 2 * M.basis.height (r.indexEquiv a) := by
    rw [latticePairing_apply, Category.assoc]
    rw [← fieldCoordinateEquiv_character M N k e τ hτ (N.rootDatum.root a)]
    rw [← latticePairing_apply, RootPairing.Hom.root_weightMap_apply]
    rw [← (M.fibrewiseRootDatum.field k).1,
      CoordinateRootDatum.fieldRealization_pairing,
      BasedBorelExponent.pairing_root_positiveCorootSum]
  have hnuTarget : latticePairing
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) N.coordinates)
      α nuTarget = 2 * N.basis.height a := by
    rw [← (N.fibrewiseRootDatum.field k).1,
      CoordinateRootDatum.fieldRealization_pairing,
      BasedBorelExponent.pairing_root_positiveCorootSum]
  have hsign := Iff.intro (hforward α hα) (hback α hα)
  rw [hnuSource, hnuTarget] at hsign
  change M.basis.IsPos (r.indexEquiv a) ↔ N.basis.IsPos a
  rw [RootPairing.Base.isPos_iff', RootPairing.Base.isPos_iff']
  omega

/-- The prescribed actual torus map identifies the simple-root supports
when its ambient comparison preserves the canonical Borels. -/
theorem fieldCoordinateEquiv_simple_iff (he : PreservesBorel e) (a : N.rootIndex) :
    a ∈ N.basis.support ↔
      (fieldCoordinateEquiv M N k e τ hτ).indexEquiv a ∈ M.basis.support :=
  StarActionIndependence.mem_support_iff_of_isPos N.basis M.basis
    (fieldCoordinateEquiv M N k e τ hτ)
    (fieldCoordinateEquiv_isPos M N k e τ hτ he) a

/-- The actual field-test comparison, torus map and based full coordinate
root equivalence, retaining their entire-character formula. -/
def fieldBasedCoordinateIso (he : PreservesBorel e) :
    BasedCoordinateIso
      (M.inclusionOver (algebraBaseMap M.ring k))
      (N.inclusionOver (algebraBaseMap N.ring k))
      M.rootDatum N.rootDatum M.basis N.basis where
  groupIso := e
  torusIso := τ
  rootEquiv := fieldCoordinateEquiv M N k e τ hτ
  sourcePairing := M.fibrewiseRootDatum.pairing k
  targetPairing := N.fibrewiseRootDatum.pairing k
  simple_iff := fieldCoordinateEquiv_simple_iff M N k e τ hτ he
  square := hτ
  characters U x m := by
    have h := congrArg (fun χ => x ≫ (CommGroupScheme.groupHom χ).hom.hom)
      (fieldCoordinateEquiv_character M N k e τ hτ m)
    have h' := congrArg (Gm.pointsEquiv (Spec (CommRingCat.of k)) U) h
    change Gm.pointsEquiv (Spec (CommRingCat.of k)) U
        (x ≫ (CommGroupScheme.groupHom
          (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
            ((fieldCoordinateEquiv M N k e τ hτ).weightMap m))).hom.hom) =
      Gm.pointsEquiv (Spec (CommRingCat.of k)) U
        ((x ≫ τ.hom.hom.hom) ≫ (CommGroupScheme.groupHom
          (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) N.coordinates m)).hom.hom) at h'
    simpa only [splitTorus.pointsEquiv_exponentCharacter] using h'.symm

end Langlands.GroupScheme.AffinePinnedModel
