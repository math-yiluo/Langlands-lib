import Langlands.GroupScheme.Reductive.AffinePinnedDisjointPinning
import Langlands.GroupScheme.Reductive.AffinePinnedAtlasInner
import Langlands.GroupScheme.Reductive.AffinePinnedSimultaneousNormalization
import Langlands.GroupScheme.Reductive.FppfLocalPinnedNormalizationStatement
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Assembly of actual local pinned corrections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T U V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

namespace Disjoint

variable {I : Type u} {Z : I → Scheme.{u}}
    (q : ∀ i, Z i ⟶ T) [IsIso (Sigma.desc q)]

private def basePointFamily
    (c : ∀ i, Over.mk (𝟙 (Z i)) ⟶ (N.groupOver (q i ≫ g)).X) (i : I) :
    Over.mk (q i ≫ 𝟙 T) ⟶ (N.groupOver g).X :=
  (Over.homMk (𝟙 (Z i)) (by simp) :
    Over.mk (q i ≫ 𝟙 T) ⟶ Over.mk (q i)) ≫
      baseChangeBasePointsEquiv (q i) (N.groupOver g)
        (c i ≫ (baseChangeCompIso g (q i) N.group).hom.hom.hom)

/-- Assemble actual target sections on direct pullbacks over a disjoint
scheme decomposition. -/
def basePoint
    (c : ∀ i, Over.mk (𝟙 (Z i)) ⟶ (N.groupOver (q i ≫ g)).X) :
    Over.mk (𝟙 T) ⟶ (N.groupOver g).X :=
  Descent.DisjointComponents.relativePoint q (𝟙 T) (basePointFamily q c)

private theorem basePoint_left
    (c : ∀ i, Over.mk (𝟙 (Z i)) ⟶ (N.groupOver (q i ≫ g)).X) (i : I) :
    q i ≫ (basePoint q c).left =
      (c i).left ≫ (baseChangeCompIso g (q i) N.group).hom.hom.hom.left ≫
        pullback.fst (N.groupOver g).X.hom (q i) := by
  have h := congrArg (fun k => k.left)
    (Descent.DisjointComponents.relativePoint_fac q (𝟙 T) (basePointFamily q c) i)
  change q i ≫ (basePoint q c).left =
    𝟙 (Z i) ≫ (baseChangeBasePointsEquiv (q i) (N.groupOver g)
      (c i ≫ (baseChangeCompIso g (q i) N.group).hom.hom.hom)).left at h
  simpa only [baseChangeBasePointsEquiv_left, Over.comp_left,
    Category.id_comp, Category.assoc] using h

/-- Every normalized component pullback recovers its supplied actual section. -/
@[simp] theorem pullBasePoint_basePoint
    (c : ∀ i, Over.mk (𝟙 (Z i)) ⟶ (N.groupOver (q i ≫ g)).X) (i : I) :
    N.pullBasePoint g (q i) (basePoint q c) = c i := by
  have h : baseChangeBasePoint (q i) (N.groupOver g) (basePoint q c) =
      c i ≫ (baseChangeCompIso g (q i) N.group).hom.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, Category.assoc, baseChangeBasePoint_fst] using
        basePoint_left q c i
    · exact (Over.w _).trans (Over.w _).symm
  unfold pullBasePoint
  rw [h]
  apply Over.OverMorphism.ext
  change (c i).left ≫ (baseChangeCompIso g (q i) N.group).hom.hom.hom.left ≫
      (baseChangeCompIso g (q i) N.group).inv.hom.hom.left = (c i).left
  have hc := congrArg (fun k => k.hom.hom.left)
    (baseChangeCompIso g (q i) N.group).hom_inv_id
  change (baseChangeCompIso g (q i) N.group).hom.hom.hom.left ≫
    (baseChangeCompIso g (q i) N.group).inv.hom.hom.left = 𝟙 _ at hc
  rw [hc, Category.comp_id]

/-- Actual target corrections that are pinned on every component give a
pinned global corrected comparison. -/
theorem corrected_isLocallyPinned (e : Comparison f g)
    (c : ∀ i, Over.mk (𝟙 (Z i)) ⟶ (N.groupOver (q i ≫ g)).X)
    (hc : ∀ i, IsLocallyPinned
      (pullComparison e (q i) ≪≫ (N.groupOver (q i ≫ g)).innerIso (c i))) :
    IsLocallyPinned (e ≪≫ (N.groupOver g).innerIso (basePoint q c)) := by
  apply isLocallyPinned_of_components q
  intro i
  rw [pullComparison_trans, pullComparison_inner, pullBasePoint_basePoint]
  exact hc i

end Disjoint

/-- An actual target section corrects the comparison to concrete local
pinning on its current common scheme. -/
def HasPinnedCorrection (e : Comparison f g) : Prop :=
  ∃ c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X,
    IsLocallyPinned (e ≪≫ (N.groupOver g).innerIso c)

private theorem pinnedCorrection_pullAlong_iff (e : Comparison f g) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    HasPinnedCorrection (pullComparisonAlong e q hf hg) ↔
      HasPinnedCorrection (pullComparison e q) := by
  subst f'
  subst g'
  rw [pullComparisonAlong_rfl]

/-- Existence of an actual pinned correction respects normalized pullback
tower coherence. -/
theorem pinnedCorrection_pullComparison_comp_iff (e : Comparison f g)
    (q : U ⟶ T) (r : V ⟶ U) :
    HasPinnedCorrection (pullComparison (pullComparison e q) r) ↔
      HasPinnedCorrection (pullComparison e (r ≫ q)) := by
  rw [← pinnedCorrection_pullAlong_iff (pullComparison e q) r
    (Category.assoc r q f).symm (Category.assoc r q g).symm,
    ← pullComparisonAlong_rfl e q, pullComparisonAlong_comp,
    pullComparisonAlong_rfl]

/-- A single fppf cover with an actual target section making the given
comparison concretely pinned. -/
structure FppfPinnedCorrection (e : Comparison f g) where
  space : Scheme.{u}
  map : space ⟶ T
  flat : Flat map
  surjective : Surjective map
  locallyOfFinitePresentation : LocallyOfFinitePresentation map
  section_ : Over.mk (𝟙 space) ⟶ (N.groupOver (map ≫ g)).X
  pinned : IsLocallyPinned
    (pullComparison e map ≪≫ (N.groupOver (map ≫ g)).innerIso section_)

namespace FppfPinnedCorrection

/-- Collapse any fppf covering family of actual pinned corrections to one
cover and one actual target section. -/
def ofCover (e : Comparison f g)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T)
    (h : ∀ i, HasPinnedCorrection (pullComparison e (𝒰.f i))) :
    FppfPinnedCorrection e := by
  let Q : (∐ 𝒰.X) ⟶ T := Sigma.desc 𝒰.f
  let q (i : 𝒰.I₀) := Sigma.ι 𝒰.X i
  haveI : IsIso (Sigma.desc q) := by
    simpa only [q, Sigma.desc_ι] using (inferInstance : IsIso (𝟙 (∐ 𝒰.X)))
  have hi (i : 𝒰.I₀) :
      HasPinnedCorrection (pullComparison (pullComparison e Q) (q i)) := by
    apply (pinnedCorrection_pullComparison_comp_iff e Q (q i)).mpr
    have hqi : q i ≫ Q = 𝒰.f i := Sigma.ι_comp_desc _ _
    exact (congrArg (fun r : 𝒰.X i ⟶ T => HasPinnedCorrection (pullComparison e r))
      hqi).mpr (h i)
  choose c hc using hi
  have hQ : Flat Q ∧ LocallyOfFinitePresentation Q :=
    𝒰.sigma.map_prop PUnit.unit
  refine {
    space := ∐ 𝒰.X
    map := Q
    flat := hQ.1
    surjective := ?_
    locallyOfFinitePresentation := hQ.2
    section_ := Disjoint.basePoint q c
    pinned := Disjoint.corrected_isLocallyPinned q (pullComparison e Q) c hc
  }
  constructor
  intro x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  exact ⟨Sigma.ι 𝒰.X i y, by
    simpa only [Q, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hy⟩

/-- The concretely pinned comparison provided by the correction. -/
def comparison {e : Comparison f g} (C : FppfPinnedCorrection e) :
    Comparison (C.map ≫ f) (C.map ≫ g) :=
  pullComparison e C.map ≪≫ (N.groupOver (C.map ≫ g)).innerIso C.section_

/-- Move the inverse target section through the supplied comparison to
obtain the exact source conjugator. -/
def sourcePoint {e : Comparison f g} (C : FppfPinnedCorrection e) :
    Over.mk (𝟙 C.space) ⟶ (M.groupOver (C.map ≫ f)).X :=
  C.section_⁻¹ ≫ (pullComparison e C.map).inv.hom.hom

/-- The source section's inner automorphism is exactly the discrepancy
between the original and pinned comparisons. -/
theorem innerIso_sourcePoint {e : Comparison f g} (C : FppfPinnedCorrection e) :
    (M.groupOver (C.map ≫ f)).innerIso C.sourcePoint =
      pullComparison e C.map ≪≫ C.comparison.symm := by
  let E := pullComparison e C.map
  apply Iso.ext
  apply (cancel_mono E.hom).mp
  have h := innerIso_hom_comp E.hom C.sourcePoint
  have hc : C.sourcePoint ≫ E.hom.hom.hom = C.section_⁻¹ := by
    have hi := congrArg (fun k => k.hom.hom) E.inv_hom_id
    simp only [Grp.comp_hom_hom, Grp.id_hom_hom] at hi
    simpa only [sourcePoint, E, Category.assoc, Category.comp_id] using
      congrArg (fun k => C.section_⁻¹ ≫ k) hi
  rw [hc] at h
  rw [h]
  simp only [E, comparison, Iso.trans_symm, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, innerIso_inv_hom]

end FppfPinnedCorrection

end Langlands.GroupScheme.AffinePinnedModel

namespace Langlands.GroupScheme

open AffinePinnedModel

/-- Actual fppf target corrections give the exact local-normalization
statement, including its source-conjugator equation. -/
theorem fppfLocalPinnedNormalization_of_pinnedCorrections
    (h : ∀ (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
      (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
      Nonempty (FppfPinnedCorrection e)) :
    FppfLocalPinnedNormalizationExistenceStatement.{u} := by
  intro M N T f g e
  let C := Classical.choice (h M N f g e)
  exact ⟨C.space, C.map, C.flat, C.surjective, C.locallyOfFinitePresentation,
    C.comparison, C.sourcePoint, C.pinned, C.innerIso_sourcePoint⟩

end Langlands.GroupScheme
