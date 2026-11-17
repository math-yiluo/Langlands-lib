import Langlands.GroupScheme.Reductive.AffinePinnedComparisonPullback
import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus

/-! # Pinned comparisons with a fixed based full root-datum equivalence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}}
  (θ : RootPairing.Equiv N.rootDatum M.rootDatum)
  (hθ : ∀ s : N.rootIndex, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support)

/-- The fixed integral character map determines an actual coordinate torus
isomorphism over every common base scheme. -/
def fixedTorusIso (T : Scheme.{u}) :
    splitTorus T M.coordinates ≅ splitTorus T N.coordinates := by
  classical
  exact LocalSplitCell.exponentEquivGroupIso T θ.weightEquiv.symm

/-- The fixed based-datum equivalence induces a fixed bijection of simple roots. -/
def fixedSimpleEquiv : N.basis.support ≃ M.basis.support :=
  θ.indexEquiv.subtypeEquiv hθ

variable {T W : Scheme.{u}} {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- The comparison induces precisely the fixed torus map, including its
whole central character lattice. -/
def PreservesFixedTorus (e : Comparison f g) : Prop :=
  M.inclusionOver f ≫ e.hom = (fixedTorusIso θ T).hom ≫ N.inclusionOver g

/-- Every affine coefficient test carries precisely the simple pinning vectors
matched by the fixed based root-datum equivalence. -/
def PreservesFixedPinning (e : Comparison f g) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra M.ring A] [Algebra N.ring A]
    (a : Spec (CommRingCat.of A) ⟶ T)
    (ha : algebraBaseMap M.ring A = a ≫ f)
    (hb : algebraBaseMap N.ring A = a ≫ g) (s : N.basis.support),
    M.rootVectorPoint f A a ha (fixedSimpleEquiv θ hθ s) ≫ e.hom.hom.hom.left =
      N.rootVectorPoint g A a hb s

/-- An actual comparison with its specified whole-lattice torus action and
fixed simple pinning-vector action. This is supplied data. -/
abbrev FixedComparison (f : T ⟶ M.base) (g : T ⟶ N.base) :=
  { e : Comparison f g // PreservesFixedTorus θ e ∧ PreservesFixedPinning θ hθ e }

/-- The fixed torus map commutes with arbitrary base change through the actual
coordinate torus base-change isomorphisms. -/
theorem fixedTorusIso_baseChange (q : W ⟶ T) :
    (GroupScheme.baseChange q).map (fixedTorusIso θ T).hom =
      (splitTorus.baseChangeIso q M.coordinates).hom ≫
        (fixedTorusIso θ W).hom ≫ (splitTorus.baseChangeIso q N.coordinates).inv := by
  classical
  exact splitTorus.baseChange_groupHom_exponentEquivIso T q θ.weightEquiv.symm

/-- A specified torus-square identity survives arbitrary common-base pullback. -/
theorem PreservesFixedTorus.pull {e : Comparison f g}
    (he : PreservesFixedTorus θ e) (q : W ⟶ T) :
    PreservesFixedTorus θ (pullComparison e q) := by
  have hτ : (splitTorus.baseChangeIso q M.coordinates).inv ≫
      (GroupScheme.baseChange q).map (fixedTorusIso θ T).hom ≫
        (splitTorus.baseChangeIso q N.coordinates).hom = (fixedTorusIso θ W).hom := by
    rw [fixedTorusIso_baseChange]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change M.inclusionOver (q ≫ f) ≫ (pullComparison e q).hom =
    (fixedTorusIso θ W).hom ≫ N.inclusionOver (q ≫ g)
  rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q, ← hτ]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    BasedBorelTransport.baseChangeInclusion, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, he, Functor.map_comp]
  simp only [Category.assoc]

/-- Each fixed simple-vector identity survives arbitrary common-base pullback. -/
theorem PreservesFixedPinning.pull {e : Comparison f g}
    (he : PreservesFixedPinning θ hθ e) (q : W ⟶ T) :
    PreservesFixedPinning θ hθ (pullComparison e q) := by
  intro A _ _ _ a ha hb s
  exact rootVectorPoint_pullComparison e q a ha hb (fixedSimpleEquiv θ hθ s) s
    (he A (a ≫ q) (by simpa only [Category.assoc] using ha)
      (by simpa only [Category.assoc] using hb) s)

/-- Pull back supplied fixed pinned comparison data along any common-base map. -/
def FixedComparison.pull (e : FixedComparison θ hθ f g) (q : W ⟶ T) :
    FixedComparison θ hθ (q ≫ f) (q ≫ g) :=
  ⟨pullComparison e.val q, e.property.1.pull θ q, e.property.2.pull θ hθ q⟩

/-- The underlying comparison is the actual normalized pullback. -/
@[simp] theorem FixedComparison.pull_val (e : FixedComparison θ hθ f g) (q : W ⟶ T) :
    (e.pull θ hθ q).val = pullComparison e.val q := rfl

/-- Pull back to explicitly equal endpoint maps with the same fixed root datum. -/
def FixedComparison.pullAlong (e : FixedComparison θ hθ f g) (q : W ⟶ T)
    {f' : W ⟶ M.base} {g' : W ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') : FixedComparison θ hθ f' g' := by
  subst f'
  subst g'
  exact e.pull θ hθ q

/-- Fixed torus preservation entails the ordinary torus-square property. -/
theorem PreservesFixedTorus.preservesTorus {e : Comparison f g}
    (he : PreservesFixedTorus θ e) : PreservesTorus e :=
  ⟨fixedTorusIso θ T, he⟩

/-- The fixed pinning correspondence gives the existing local affine-test
pinning property by its one specified bijection. -/
theorem PreservesFixedPinning.preservesLocalPinning {e : Comparison f g}
    (he : PreservesFixedPinning θ hθ e) : PreservesLocalPinning e := by
  intro A _ _ _ _ a ha hb
  refine ⟨(fixedSimpleEquiv θ hθ).symm, fun s => ?_⟩
  simpa only [Equiv.apply_symm_apply] using
    he A a ha hb ((fixedSimpleEquiv θ hθ).symm s)

end Langlands.GroupScheme.AffinePinnedModel
