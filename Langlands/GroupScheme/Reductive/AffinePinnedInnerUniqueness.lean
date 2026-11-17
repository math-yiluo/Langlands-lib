import Langlands.GroupScheme.Reductive.AffinePinnedInnerPinning
import Langlands.GroupScheme.Reductive.RelativePinnedNormalizationDescent

/-! # Rigidity and uniqueness of pinned inner comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A torus representative of a pinning-preserving self-comparison lies in the
full relative centre on every scheme test. -/
theorem mem_center_of_torus_representsIso
    (e : Comparison f f) (he : PreservesLocalPinning e)
    {V : Over T} (t : V ⟶ (splitTorus T M.coordinates).X)
    (ht : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso e
      (t ≫ (M.inclusionOver f).hom.hom)) :
    t ≫ (M.inclusionOver f).hom.hom ∈ (center (M.groupOver f)).carrier V := by
  intro W q z
  change (q ≫ t ≫ (M.inclusionOver f).hom.hom) * z =
    z * (q ≫ t ≫ (M.inclusionOver f).hom.hom)
  apply (baseChangePointsEquiv f M.group W).injective
  apply Over.OverMorphism.ext
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  apply CellGluing.hom_ext_of_closedResidueLocalRingPoints
  intro A _ _ _ a
  let s := a ≫ W.hom
  let : Algebra M.ring A := (Spec.preimage (s ≫ f)).hom.toAlgebra
  have ha : algebraBaseMap M.ring A = s ≫ f := Spec.map_preimage _
  let r : Over.mk s ⟶ W := Over.homMk a rfl
  let tA := r ≫ q ≫ t
  have htA :
      (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso e
        (tA ≫ (M.inclusionOver f).hom.hom) := by
    intro Z b x
    simpa only [tA, Category.assoc] using ht (b ≫ r ≫ q) x
  let E := coefficientTestPointsEquiv f A s ha M.group
  have hc := mem_center_coefficientTest_of_representsIso f A s ha e he tA htA
  have hce := hc _ (𝟙 _) (E (r ≫ z))
  simp only [Category.id_comp] at hce
  have hlocal :
      (r ≫ q ≫ t ≫ (M.inclusionOver f).hom.hom) * (r ≫ z) =
        (r ≫ z) * (r ≫ q ≫ t ≫ (M.inclusionOver f).hom.hom) := by
    apply E.injective
    simpa only [map_mul, E, tA, Category.assoc] using hce.eq
  have hpre :
      r ≫ ((q ≫ t ≫ (M.inclusionOver f).hom.hom) * z) =
        r ≫ (z * (q ≫ t ≫ (M.inclusionOver f).hom.hom)) := by
    simpa only [MonObj.comp_mul, Category.assoc] using hlocal
  have hp := congrArg
    (fun k => k.left ≫ pullback.fst M.group.X.hom f) hpre
  change (a ≫ _) ≫ _ = (a ≫ _) ≫ _ at hp
  simpa only [baseChangePointsEquiv_left, Category.assoc] using hp

/-- Every representative of an inner self-comparison preserving the
cocharacter and pinning belongs to the full relative centre. -/
theorem mem_center_of_representsIso
    (e : Comparison f f) (hco : PreservesCocharacter e)
    (hpin : PreservesLocalPinning e)
    {V : Over T} (y : V ⟶ (M.groupOver f).X)
    (hy : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso e y) :
    y ∈ (center (M.groupOver f)).carrier V := by
  let t := torusConjugator hco y hy
  have ht : t ≫ (M.inclusionOver f).hom.hom = y :=
    torusConjugator_comp hco y hy
  rw [← ht]
  exact mem_center_of_torus_representsIso e hpin t (ht.symm ▸ hy)

/-- A concretely pinned locally inner self-comparison is the identity. -/
theorem eq_refl_of_locallyPinned_locallyInner
    {e : Comparison f f} (he : IsLocallyPinned e)
    (hi : IsFppfLocallyInner e) : e = Iso.refl (M.groupOver f) := by
  obtain ⟨V, hf, hs, hl, y, hy⟩ := hi
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : LocallyOfFinitePresentation V.hom := hl
  have hcent := mem_center_of_representsIso e he.2.1 he.2.2 y hy
  apply Iso.ext
  apply hom_ext_points
  intro W z
  let Z : Over T := Over.mk (pullback.fst W.hom V.hom ≫ W.hom)
  let r : Z ⟶ W := Over.homMk (pullback.fst W.hom V.hom) rfl
  let a : Z ⟶ V := Over.homMk (pullback.snd W.hom V.hom) pullback.condition.symm
  have : Epi r.left := by
    change Epi (pullback.fst W.hom V.hom)
    infer_instance
  have : Epi r := Over.epi_of_epi_left r
  apply (cancel_epi r).mp
  have hc := hy a (r ≫ z)
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id] at hc
  rw [(hcent Z a (r ≫ z)).eq, mul_inv_cancel_right] at hc
  simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.comp_id, Category.assoc]
    using hc.symm

/-- Concrete pinned comparisons in the same local-inner class coincide. -/
theorem eq_of_locallyPinned_innerEquivalent
    {e d : Comparison f g} (he : IsLocallyPinned e)
    (hd : IsLocallyPinned d) (hi : IsFppfInnerEquivalent e d) : e = d := by
  have h := eq_refl_of_locallyPinned_locallyInner (he.trans hd.symm) hi
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans]
    using congrArg (fun k => k ≪≫ d) h

/-- Fppf-local pinning is enough for rigidity of a locally inner
self-comparison, by faithful pullback along its pinning cover. -/
theorem eq_refl_of_fppfLocallyPinned_locallyInner
    {e : Comparison f f} (he : IsFppfLocallyPinned e)
    (hi : IsFppfLocallyInner e) : e = Iso.refl (M.groupOver f) := by
  obtain ⟨U, q, hf, hs, hl, hq⟩ := he
  let : Flat q := hf
  let : Surjective q := hs
  let : LocallyOfFinitePresentation q := hl
  have hi' : IsFppfInnerEquivalent e (Iso.refl (M.groupOver f)) := by
    simpa only [IsFppfInnerEquivalent, Iso.refl_symm, Iso.trans_refl] using hi
  have hqinner : IsFppfLocallyInner (pullComparison e q) := by
    simpa only [IsFppfInnerEquivalent, pullComparison_refl, Iso.refl_symm,
      Iso.trans_refl] using innerEquivalent_pullComparison hi' q
  apply pullComparison_injective q
  change pullComparison e q = pullComparison (Iso.refl (M.groupOver f)) q
  rw [pullComparison_refl]
  exact eq_refl_of_locallyPinned_locallyInner hq hqinner

/-- Fppf-locally pinned comparisons in the same local-inner class coincide. -/
theorem eq_of_fppfLocallyPinned_innerEquivalent
    {e d : Comparison f g} (he : IsFppfLocallyPinned e)
    (hd : IsFppfLocallyPinned d) (hi : IsFppfInnerEquivalent e d) : e = d := by
  have h := eq_refl_of_fppfLocallyPinned_locallyInner (he.trans hd.symm) hi
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans]
    using congrArg (fun k => k ≪≫ d) h

/-- Each local-inner class has at most one fppf-locally pinned comparison.
Existence of such a comparison is a separate condition. -/
def PinnedInnerRigidity : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e d : Comparison f g),
    IsFppfLocallyPinned e → IsFppfLocallyPinned d →
      IsFppfInnerEquivalent e d → e = d

/-- Rigidity holds for all supplied models and every scheme test. -/
theorem pinnedInnerRigidity : PinnedInnerRigidity.{u} := by
  intro M N T f g e d he hd hi
  exact eq_of_fppfLocallyPinned_innerEquivalent he hd hi

end Langlands.GroupScheme.AffinePinnedModel
