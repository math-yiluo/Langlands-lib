import Langlands.GroupScheme.Reductive.PinnedComparisonLabels
import Langlands.GroupScheme.Reductive.AffinePinnedWeightTransport
import Langlands.GroupScheme.Reductive.AffinePinnedTorusPinning
import Langlands.GroupScheme.Reductive.LocalSplitLocalAlgebraCellIsomorphism

/-! # Local completeness of full weight labels for pinned comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

/-- A nonzero chosen simple vector determines its entire integral weight
over every nonzero coefficient ring. -/
theorem simpleVector_weight_eq (M : AffinePinnedModel.{u}) [Nontrivial M.ring]
    (s : M.basis.support) (m : M.coordinates → ℤ)
    (hm : (M.pinning s 1).val ∈
      splitTorus.exponentWeightSpace M.coordinates M.group M.inclusion m) :
    m = M.rootDatum.root s := by
  classical
  let : Smooth M.group.X.hom := M.reductive.smooth
  by_contra hne
  have he := (splitTorus.universalAdjointCoefficients_of_mem_exponentWeightSpace
    M.coordinates M.group M.inclusion m (M.pinning s 1).val hm).symm.trans
      (splitTorus.universalAdjointCoefficients_of_mem_exponentWeightSpace
        M.coordinates M.group M.inclusion (M.rootDatum.root s)
        (M.pinning s 1).val (M.pinning s 1).property)
  have hv := congrArg (fun z => z (M.rootDatum.root s)) he
  rw [Finsupp.single_eq_of_ne (Ne.symm hne), Finsupp.single_eq_same] at hv
  have hz : M.pinning s 1 = 0 := Subtype.ext hv.symm
  exact one_ne_zero ((M.pinning s).injective (hz.trans (map_zero _).symm))

local instance scalarAffineLocalLabels (P : AffinePinnedModel.{u})
    (A : Type u) [CommRing A] [Algebra P.ring A] :
    IsAffineHom (P.groupOver (algebraBaseMap P.ring A)).X.hom :=
  (P.reductive.baseChange (algebraBaseMap P.ring A)).isAffineHom

variable {M N : AffinePinnedModel.{u}}
  (θ : RootPairing.Equiv N.rootDatum M.rootDatum)
  (hθ : ∀ s, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support)

/-- On a local coefficient ring, concrete local pinning and an exact full
torus map give the fixed affine theorem's exact differential equations. -/
theorem isAffineSolution_of_fixedTorus_locallyPinned
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (ht : PreservesFixedTorus θ e) (hp : PreservesLocalPinning e) :
    IsAffineSolution θ hθ A e := by
  refine ⟨⟨fixedTorusIso θ _, ht, fixedTorusIso_characters θ _⟩, ?_⟩
  obtain ⟨σ, hσ⟩ := hp A (𝟙 _) (by simp) (by simp)
  have hv (s : M.basis.support) :
      Lie.targetMapLinear e.hom A ((M.scalarExtension A).pinning s 1).val =
        ((N.scalarExtension A).pinning (σ s) 1).val := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change (((M.scalarExtension A).pinning s 1).val.toMul.val).left ≫
        e.hom.hom.hom.left =
      (((N.scalarExtension A).pinning (σ s) 1).val.toMul.val).left
    rw [scalarExtension_pinning_point, scalarExtension_pinning_point]
    exact hσ s
  intro s
  let t := fixedSimpleEquiv θ hθ s
  have hw : Lie.targetMapLinear e.hom A ((M.scalarExtension A).pinning t 1).val ∈
      splitTorus.exponentWeightSpace N.coordinates
        (N.groupOver (algebraBaseMap N.ring A))
        (N.inclusionOver (algebraBaseMap N.ring A)) (N.rootDatum.root s) := by
    apply splitTorus.mem_exponentWeightSpace_of_transport e.hom
      (fixedTorusIso θ _) ht (M.rootDatum.root t) (N.rootDatum.root s) ?_
      ((M.scalarExtension A).pinning t 1).property
    intro B _ _ x
    apply splitTorus.exponentValue_transport_of_points
      (fixedTorusIso θ _) (M.rootDatum.root t) (N.rootDatum.root s) ?_ B x
    intro U z
    have h := fixedTorusIso_characters θ _ U z (N.rootDatum.root s)
    have hr : θ.weightMap (N.rootDatum.root s) = M.rootDatum.root t :=
      RootPairing.Hom.root_weightMap_apply N.rootDatum M.rootDatum s θ.toHom
    simpa only [hr] using h
  rw [hv] at hw
  let : Nontrivial (N.scalarExtension A).ring := inferInstanceAs (Nontrivial A)
  have hr := simpleVector_weight_eq (N.scalarExtension A) (σ t)
    (N.rootDatum.root s) hw
  have hs : s = σ t := Subtype.ext (N.rootDatum.root.injective hr)
  exact (hv t).trans
    (congrArg (fun s => ((N.scalarExtension A).pinning s 1).val) hs.symm)

variable {T : Scheme.{u}} {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Equality after every local coefficient pullback detects equality of
actual comparisons on an arbitrary common scheme, including nilpotents. -/
theorem comparison_eq_of_localRing_pull {e d : Comparison f g}
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (a : Spec (CommRingCat.of A) ⟶ T),
      pullComparison e a = pullComparison d a) : e = d := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · let : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
    apply CellGluing.hom_ext_of_localRingPoints
    intro A _ _ a
    let b := a ≫ (M.groupOver f).X.hom
    let z : Over.mk b ⟶ (M.groupOver f).X := Over.homMk a rfl
    have he := congrArg
      (fun k : Comparison (b ≫ f) (b ≫ g) =>
        (comparisonLocalIso b k).toFun (𝟙 (Over.mk b)) z) (h A b)
    simp only [comparisonLocalIso, comparisonToIterated_pullComparison] at he
    have he' : z ≫ e.hom.hom.hom = z ≫ d.hom.hom.hom :=
      (LocalGroupIso.ofBaseChangeIso_mapIso_toFun (U := Over.mk b)
        e (𝟙 (Over.mk b)) z).symm.trans
          (he.trans (LocalGroupIso.ofBaseChangeIso_mapIso_toFun (U := Over.mk b)
            d (𝟙 (Over.mk b)) z))
    have hl := congrArg (fun k => k.left ≫ pullback.fst N.group.X.hom g) he'
    simpa only [z, Over.comp_left, Over.homMk_left, Category.assoc] using hl
  · exact (Over.w e.hom.hom.hom).trans (Over.w d.hom.hom.hom).symm

/-- The specified full torus equation persists under pullback with
explicitly reindexed endpoint maps. -/
theorem PreservesFixedTorus.pullAlong {e : Comparison f g}
    (ht : PreservesFixedTorus θ e) {W : Scheme.{u}} (a : W ⟶ T)
    {f' : W ⟶ M.base} {g' : W ⟶ N.base}
    (hf : a ≫ f = f') (hg : a ≫ g = g') :
    PreservesFixedTorus θ (pullComparisonAlong e a hf hg) := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using ht.pull θ a

/-- A concretely locally pinned comparison with a fixed entire torus map
is the canonical fixed comparison on the whole arbitrary common scheme. -/
theorem eq_fixedComparison_of_locallyPinned
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (e : Comparison f g) (he : IsLocallyPinned e)
    (ht : PreservesFixedTorus θ e) :
    e = (fixedComparison θ hθ hAffine f g).val := by
  let d := fixedComparison θ hθ hAffine f g
  apply comparison_eq_of_localRing_pull
  intro A _ _ a
  let : Algebra M.ring A := (Spec.preimage (a ≫ f)).hom.toAlgebra
  let : Algebra N.ring A := (Spec.preimage (a ≫ g)).hom.toAlgebra
  have hf : a ≫ f = algebraBaseMap M.ring A := (Spec.map_preimage _).symm
  have hg : a ≫ g = algebraBaseMap N.ring A := (Spec.map_preimage _).symm
  have hsol := isAffineSolution_of_fixedTorus_locallyPinned θ hθ A
    (pullComparisonAlong e a hf hg) (ht.pullAlong θ a hf hg)
    (he.pullAlong a hf hg).2.2
  have huniq := ExistsUnique.unique (existsUnique_affineSolution θ hθ A hAffine)
    hsol ((d.pullAlong θ hθ a hf hg).isAffineSolution θ hθ A)
  rw [FixedComparison.pullAlong_val] at huniq
  exact (pullComparisonAlong_eq_iff e d.val a hf hg).mp huniq

/-- Every concretely locally pinned comparison equals a single canonical
full-weight representative on a neighbourhood of each point. -/
theorem exists_open_comparisonLabel
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (e : Comparison f g) (he : IsLocallyPinned e) (x : T) :
    ∃ U : T.Opens, x ∈ U ∧ ∃ d : ComparisonLabel M N,
      pullComparison e U.ι = d.representative hAffine (U.ι ≫ f) (U.ι ≫ g) := by
  obtain ⟨τ, hτ⟩ := he.1
  obtain ⟨U, hxU, a, hae, _⟩ :=
    exists_open_basedCoordinateIso e τ hτ he.2.1.preservesBorel x
  let d : ComparisonLabel M N :=
    ⟨a.rootEquiv.weightEquiv,
      a.rootEquiv, rfl, a.simple_iff, a.sourcePairing, a.targetPairing⟩
  have hw (m : N.coordinates → ℤ) :
      d.rootEquiv.weightMap m = a.rootEquiv.weightMap m := by
    change d.rootEquiv.weightEquiv m = a.rootEquiv.weightEquiv m
    rw [d.rootEquiv_weightEquiv]
  have hc : ∀ (V : Over (U : Scheme))
      (t : V ⟶ (splitTorus U M.coordinates).X) (m : N.coordinates → ℤ),
      ∏ j, splitTorus.pointsEquiv N.coordinates V (t ≫ a.torusIso.hom.hom.hom) j ^ m j =
        ∏ i, splitTorus.pointsEquiv M.coordinates V t i ^ d.rootEquiv.weightMap m i := by
    intro V t m
    rw [hw]
    exact a.characters V t m
  have htorus := torusIso_eq_fixedTorusIso_of_characters d.rootEquiv a.torusIso hc
  have ht : PreservesFixedTorus d.rootEquiv (pullComparison e U.ι) := by
    have hs := a.square
    rw [hae, htorus] at hs
    exact hs
  exact ⟨U, hxU, d,
    eq_fixedComparison_of_locallyPinned d.rootEquiv d.simple_iff hAffine
      (pullComparison e U.ι) (he.pull U.ι) ht⟩

/-- An open neighbourhood with one full lattice label and the exact
comparison equation, for the supplied comparison and point. -/
structure LabeledComparisonNeighbourhood
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (e : Comparison f g) (x : T) where
  neighbourhood : T.Opens
  mem_neighbourhood : x ∈ neighbourhood
  label : ComparisonLabel M N
  comparison_eq : pullComparison e neighbourhood.ι =
    label.representative hAffine (neighbourhood.ι ≫ f) (neighbourhood.ι ≫ g)

/-- Choose the labelled open neighbourhood of a concretely locally pinned
comparison, retaining its exact equality and the supplied point. -/
def labeledComparisonNeighbourhood
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (e : Comparison f g) (he : IsLocallyPinned e) (x : T) :
    LabeledComparisonNeighbourhood hAffine e x :=
  Classical.choice <| by
    obtain ⟨U, hxU, d, hd⟩ := exists_open_comparisonLabel hAffine e he x
    exact ⟨⟨U, hxU, d, hd⟩⟩

end Langlands.GroupScheme.AffinePinnedModel
