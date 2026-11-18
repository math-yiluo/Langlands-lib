import Langlands.GroupScheme.Reductive.PinnedComparisonConstantFamily
import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartStatement

/-! # Descent of pinned comparison labels to every original test -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

open Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

/-- The local completeness input: concretely pinned comparisons agree with
canonical full-lattice representatives on a neighbourhood of each point. -/
def OpenPinnedLabelCompleteness (M N : AffinePinnedModel.{u})
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    IsLocallyPinned e → ∀ x : T, ∃ U : T.Opens, x ∈ U ∧
      ∃ d : ComparisonLabel M N,
        pullComparison e U.ι = d.representative hAffine (U.ι ≫ f) (U.ι ≫ g)

private theorem label_eq_pullAlong {M N : AffinePinnedModel.{u}}
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    {T W : Scheme.{u}} {f : T ⟶ M.base} {g : T ⟶ N.base}
    {e : Comparison f g} (d : ComparisonLabel M N) (q : W ⟶ T)
    (h : pullComparison e q = d.representative hAffine (q ≫ f) (q ≫ g))
    {f' : W ⟶ M.base} {g' : W ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    pullComparisonAlong e q hf hg = d.representative hAffine f' g' := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using h

variable (M N : AffinePinnedModel.{u})
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    {S : Scheme.{u}} (f : S ⟶ M.base) (g : S ⟶ N.base)

/-- A constant label on a relative test, as a morphism to the actual constant scheme. -/
def pinnedLabelPoint (T : Over S) (d : ComparisonLabel M N) :
    T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N) :=
  LocalGroupIso.terminalBasePoint T ≫ sigmaOverι (fun _ => Over.mk (𝟙 S)) d

/-- Constant labels evaluate to their prescribed all-test representative families. -/
theorem constantPinnedFamily_refine_labelPoint (T : Over S) (d : ComparisonLabel M N) :
    (constantPinnedFamily M N hAffine f g).refine (pinnedLabelPoint M N T d) =
      d.localFamily hAffine f g T := by
  change (LocalGroupIso.coproduct (fun _ => Over.mk (𝟙 S))
    (fun d : ComparisonLabel M N => d.localFamily hAffine f g (Over.mk (𝟙 S)))).refine
      (LocalGroupIso.terminalBasePoint T ≫ sigmaOverι (fun _ => Over.mk (𝟙 S)) d) = _
  rw [← LocalGroupIso.refine_comp, LocalGroupIso.coproduct_refine_ι]
  exact d.localFamily_refine hAffine f g (LocalGroupIso.terminalBasePoint T)

variable (hcomplete : OpenPinnedLabelCompleteness M N hAffine)

include hcomplete in
/-- The local completeness input classifies concretely pinned families by a
unique constant-scheme morphism on the original, arbitrary relative test. -/
theorem existsUnique_label_of_locallyPinned (T : Over S)
    (F : LocalGroupIso (M.groupOver f) (N.groupOver g) T)
    (hF : IsLocallyPinned (comparisonFromIterated T.hom F.toBaseChangeIso)) :
    ∃! b : T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N),
      (constantPinnedFamily M N hAffine f g).refine b = F := by
  classical
  let c := comparisonFromIterated T.hom F.toBaseChangeIso
  have hl := hcomplete T.left (T.hom ≫ f) (T.hom ≫ g) c hF
  choose U hU d hd using hl
  let V (x : T.left) : Over S := Over.mk ((U x).ι ≫ T.hom)
  let p (x : T.left) : V x ⟶ T := Over.homMk (U x).ι rfl
  let 𝒰 : T.left.OpenCover := Scheme.Cover.mkOfCovers T.left
    (fun x => (U x : Scheme.{u})) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hU x⟩, rfl⟩)
  have hp : Sieve.ofArrows V p ∈ Scheme.zariskiTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact 𝒰.mem_grothendieckTopology
  apply LocalGroupIso.existsUnique_classify_of_cover
    (constantPinnedFamily M N hAffine f g)
    (constantPinnedFamily_refine_injective M N hAffine f g)
    (Scheme.zariskiTopology.over S) V p hp F
    (fun x => pinnedLabelPoint M N (V x) (d x))
  intro x
  rw [constantPinnedFamily_refine_labelPoint]
  apply LocalGroupIso.baseChangeIsoEquiv.symm.injective
  change (d x |>.localFamily hAffine f g (V x)).toBaseChangeIso =
    (F.refine (p x)).toBaseChangeIso
  rw [ComparisonLabel.localFamily, LocalGroupIso.toBaseChangeIso_ofBaseChangeIso,
    LocalGroupIso.toBaseChangeIso_refine]
  rw [← comparisonToIterated_fromIterated T.hom F.toBaseChangeIso,
    ← comparisonToIterated_pullAlong T.hom (p x).left (V x).hom (Over.w (p x))]
  congr 1
  symm
  exact label_eq_pullAlong hAffine (d x) (p x).left (hd x) _ _

include hcomplete in
/-- Fppf-local concrete pinning already has a unique label on the original
test; the label is descended as a morphism into the actual constant scheme. -/
theorem existsUnique_label_of_fppfLocallyPinned (T : Over S)
    (F : LocalGroupIso (M.groupOver f) (N.groupOver g) T)
    (hF : IsFppfLocallyPinned (comparisonFromIterated T.hom F.toBaseChangeIso)) :
    ∃! b : T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N),
      (constantPinnedFamily M N hAffine f g).refine b = F := by
  obtain ⟨U, q, hqf, hqs, hql, hq⟩ := hF
  let : Flat q := hqf
  let : Surjective q := hqs
  let : LocallyOfFinitePresentation q := hql
  let W : Over S := Over.mk (q ≫ T.hom)
  let p : W ⟶ T := Over.homMk q rfl
  have hW : IsLocallyPinned (comparisonFromIterated W.hom (F.refine p).toBaseChangeIso) := by
    rw [LocalGroupIso.toBaseChangeIso_refine, comparisonFromIterated_pullAlong]
    simpa only [W, p, Over.homMk_left, Category.assoc, pullComparisonAlong_rfl] using hq
  obtain ⟨b, hb, _⟩ := existsUnique_label_of_locallyPinned M N hAffine f g hcomplete W
    (F.refine p) hW
  have hp : Sieve.ofArrows (fun _ : PUnit.{1} => W) (fun _ => p) ∈
      Scheme.fppfTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => q)) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact Precoverage.generate_mem_toGrothendieck q.singleton_mem_fppfPrecoverage
  exact LocalGroupIso.existsUnique_classify_of_cover
    (constantPinnedFamily M N hAffine f g)
    (constantPinnedFamily_refine_injective M N hAffine f g)
    (Scheme.fppfTopology.over S) (fun _ : PUnit.{1} => W) (fun _ => p) hp F
    (fun _ => b) (fun _ => hb)

/-- Choose the unique original-test label for an fppf-locally pinned comparison. -/
def classifyPinnedFamily (T : Over S)
    (F : LocalGroupIso (M.groupOver f) (N.groupOver g) T)
    (hF : IsFppfLocallyPinned (comparisonFromIterated T.hom F.toBaseChangeIso)) :
    T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N) :=
  (existsUnique_label_of_fppfLocallyPinned M N hAffine f g hcomplete T F hF).choose

@[simp] theorem refine_classifyPinnedFamily (T : Over S)
    (F : LocalGroupIso (M.groupOver f) (N.groupOver g) T)
    (hF : IsFppfLocallyPinned (comparisonFromIterated T.hom F.toBaseChangeIso)) :
    (constantPinnedFamily M N hAffine f g).refine
      (classifyPinnedFamily M N hAffine f g hcomplete T F hF) = F :=
  (existsUnique_label_of_fppfLocallyPinned M N hAffine f g hcomplete T F hF).choose_spec.1

include hcomplete in
/-- Local label completeness and local pinned normalization yield the full
representation-free adjoint/constant-label decomposition on every scheme test. -/
theorem constantPinnedFamily_orbit_bijective
    (hlocal : HasFppfLocalPinnedRepresentatives.{u})
    {A : GroupScheme S} {q : M.groupOver f ⟶ A} (hq : IsRelativeAdjointQuotient q)
    (T : Over S) : Function.Bijective
      (fun z : (T ⟶ A.X) ×
          (T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N)) =>
        ((constantPinnedFamily M N hAffine f g).refine z.2).twist hq.innerAction z.1⁻¹) := by
  let n := normalizationOfLocalPinnedRepresentatives hlocal
  let na := n.actualNormalization M N f g
  apply na.localOrbit_bijective hq (constantPinnedFamily M N hAffine f g)
  · exact constantPinnedFamily_normalized M N hAffine f g n
      (fun d T => (d.representative_isLocallyPinned hAffine (T.hom ≫ f)
        (T.hom ≫ g)).fppfLocallyPinned)
  · intro W F
    apply existsUnique_label_of_fppfLocallyPinned M N hAffine f g hcomplete W
      (na.localNormalize W F)
    rw [GroupIsomorphismScheme.ActualNormalization.localNormalize_toBaseChangeIso]
    change IsFppfLocallyPinned (comparisonFromIterated W.hom
      (comparisonToIterated W.hom (n.correction M N (W.hom ≫ f) (W.hom ≫ g)
        (comparisonFromIterated W.hom F.toBaseChangeIso))))
    rw [comparisonFromIterated_toIterated]
    exact (n.correction_spec M N (W.hom ≫ f) (W.hom ≫ g)
      (comparisonFromIterated W.hom F.toBaseChangeIso)).1

end Langlands.GroupScheme.AffinePinnedModel

namespace Langlands.GroupScheme

/-- Conditional assembly of the exact chart statement. The two classification
inputs remain explicit, and the supplied quotient and representer are arbitrary. -/
theorem pinnedOuterIsomorphismChart_of_localCompleteness
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : AffinePinnedModel.HasFppfLocalPinnedRepresentatives.{u})
    (hcomplete : ∀ M N : AffinePinnedModel.{u},
      AffinePinnedModel.OpenPinnedLabelCompleteness M N hAffine) :
    PinnedOuterIsomorphismChartStatement.{u} := by
  intro M N S f g A q hq I
  let E := AffinePinnedModel.constantPinnedFamily M N hAffine f g
  refine ⟨AffinePinnedModel.ComparisonLabel M N, I.classify E, ?_⟩
  exact I.orbit_bijective_of_local hq.innerAction E
    (AffinePinnedModel.constantPinnedFamily_orbit_bijective M N hAffine f g
      (hcomplete M N) hlocal hq)

end Langlands.GroupScheme
