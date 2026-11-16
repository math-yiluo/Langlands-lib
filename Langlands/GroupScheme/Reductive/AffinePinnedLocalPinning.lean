import Langlands.GroupScheme.Reductive.AffinePinnedRootVectors
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonProperties
import Mathlib.RingTheory.LocalRing.Basic

/-! # Pinning preservation on arbitrary local affine tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N K : AffinePinnedModel.{u}} {T W : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base} {h : T ⟶ K.base}

/-- On each local affine test, the actual differential carries the original
simple pinning vectors to the target vectors with some bijective relabelling.
The relabelling is allowed to depend on the test. -/
def PreservesLocalPinning (e : Comparison f g) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (a : Spec (CommRingCat.of A) ⟶ T)
    (ha : algebraBaseMap M.ring A = a ≫ f)
    (hb : algebraBaseMap N.ring A = a ≫ g),
    ∃ σ : M.basis.support ≃ N.basis.support, ∀ s,
      M.rootVectorPoint f A a ha s ≫ e.hom.hom.hom.left =
        N.rootVectorPoint g A a hb (σ s)

@[simp]
theorem preservesLocalPinning_refl (M : AffinePinnedModel.{u})
    (f : T ⟶ M.base) : PreservesLocalPinning (Iso.refl (M.groupOver f)) := by
  intro A _ _ α β a ha hb
  have hαβ : α = β := by
    apply Algebra.algebra_ext
    intro r
    have hm := congrArg
      (fun z : Spec (CommRingCat.of A) ⟶ M.base => (Spec.preimage z).hom r)
      (ha.trans hb.symm)
    simp only [algebraBaseMap, Spec.preimage_map] at hm
    change α.algebraMap r = β.algebraMap r at hm
    exact hm
  cases hαβ
  refine ⟨Equiv.refl _, fun s => ?_⟩
  change _ ≫ (𝟙 (M.groupOver f).X.left) = _
  exact Category.comp_id _

/-- A missing intermediate coefficient structure is recovered from the actual
affine test map to the intermediate model's original base. -/
theorem PreservesLocalPinning.trans {e : Comparison f g} {d : Comparison g h}
    (he : PreservesLocalPinning e) (hd : PreservesLocalPinning d) :
    PreservesLocalPinning (e ≪≫ d) := by
  intro A _ _ _ _ a ha hc
  let : Algebra N.ring A := (Spec.preimage (a ≫ g)).hom.toAlgebra
  have hb : algebraBaseMap N.ring A = a ≫ g := Spec.map_preimage _
  obtain ⟨σ, hσ⟩ := he A a ha hb
  obtain ⟨τ, hτ⟩ := hd A a hb hc
  refine ⟨σ.trans τ, fun s => ?_⟩
  change M.rootVectorPoint f A a ha s ≫
    e.hom.hom.hom.left ≫ d.hom.hom.hom.left = _
  rw [← Category.assoc, hσ, hτ]
  rfl

/-- Actual point transport for one simple-vector equation. -/
theorem rootVectorPoint_pullComparison
    {A : Type u} [CommRing A] [Algebra M.ring A] [Algebra N.ring A]
    (e : Comparison f g) (q : W ⟶ T)
    (a : Spec (CommRingCat.of A) ⟶ W)
    (ha : algebraBaseMap M.ring A = a ≫ (q ≫ f))
    (hb : algebraBaseMap N.ring A = a ≫ (q ≫ g))
    (s : M.basis.support) (t : N.basis.support)
    (hv : M.rootVectorPoint f A (a ≫ q)
        (by simpa only [Category.assoc] using ha) s ≫ e.hom.hom.hom.left =
      N.rootVectorPoint g A (a ≫ q)
        (by simpa only [Category.assoc] using hb) t) :
    M.rootVectorPoint (q ≫ f) A a ha s ≫
        (pullComparison e q).hom.hom.hom.left =
      N.rootVectorPoint (q ≫ g) A a hb t := by
  have heq : (pullComparison e q).hom ≫ (baseChangeCompIso g q N.group).hom =
      (baseChangeCompIso f q M.group).hom ≫ (baseChange q).map e.hom := by
    simp [pullComparison]
  have heq' := congrArg (fun k => k.hom.hom.left) heq
  change (pullComparison e q).hom.hom.hom.left ≫
    (baseChangeCompIso g q N.group).hom.hom.hom.left =
    (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
      ((baseChange q).map e.hom).hom.hom.left at heq'
  have hmap : ((baseChange q).map e.hom).hom.hom.left ≫
        pullback.fst (N.groupOver g).X.hom q =
      pullback.fst (M.groupOver f).X.hom q ≫ e.hom.hom.hom.left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  apply (cancel_mono (baseChangeCompIso g q N.group).hom.hom.hom.left).mp
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [← Category.assoc (pullComparison e q).hom.hom.hom.left, heq',
      Category.assoc, hmap, N.rootVectorPoint_pull g A q a hb t]
    have hp := congrArg (fun k => k ≫ e.hom.hom.hom.left)
      (M.rootVectorPoint_pull f A q a ha s)
    simpa only [Category.assoc] using hp.trans hv
  · have hcomp := Over.w (baseChangeCompIso g q N.group).hom.hom.hom
    have heover := Over.w (pullComparison e q).hom.hom.hom
    change _ ≫ (N.groupOver (q ≫ g)).X.hom =
      (M.groupOver (q ≫ f)).X.hom at heover
    change _ ≫ pullback.snd (N.groupOver g).X.hom q =
      (N.groupOver (q ≫ g)).X.hom at hcomp
    simp only [Category.assoc]
    rw [hcomp, heover, rootVectorPoint_snd, rootVectorPoint_snd]

/-- Pinning preservation on local affine tests survives arbitrary pullback. -/
theorem PreservesLocalPinning.pull {e : Comparison f g}
    (he : PreservesLocalPinning e) (q : W ⟶ T) :
    PreservesLocalPinning (pullComparison e q) := by
  intro A _ _ _ _ a ha hb
  obtain ⟨σ, hσ⟩ := he A (a ≫ q)
    (by simpa only [Category.assoc] using ha)
    (by simpa only [Category.assoc] using hb)
  exact ⟨σ, fun s => rootVectorPoint_pullComparison e q a ha hb s (σ s) (hσ s)⟩

/-- A concrete candidate for pinned normalization. Its geometric local
existence and uniqueness are separate obligations. -/
def IsLocallyPinned (e : Comparison f g) : Prop :=
  PreservesTorus e ∧ PreservesCocharacter e ∧ PreservesLocalPinning e

@[simp]
theorem isLocallyPinned_refl (M : AffinePinnedModel.{u}) (f : T ⟶ M.base) :
    IsLocallyPinned (Iso.refl (M.groupOver f)) :=
  ⟨preservesTorus_refl M f, preservesCocharacter_refl M f,
    preservesLocalPinning_refl M f⟩

theorem IsLocallyPinned.trans {e : Comparison f g} {d : Comparison g h}
    (he : IsLocallyPinned e) (hd : IsLocallyPinned d) : IsLocallyPinned (e ≪≫ d) :=
  ⟨he.1.trans hd.1, he.2.1.trans hd.2.1, he.2.2.trans hd.2.2⟩

theorem IsLocallyPinned.pull {e : Comparison f g} (he : IsLocallyPinned e)
    (q : W ⟶ T) : IsLocallyPinned (pullComparison e q) :=
  ⟨he.1.pull q, he.2.1.pull q, he.2.2.pull q⟩

end Langlands.GroupScheme.AffinePinnedModel
