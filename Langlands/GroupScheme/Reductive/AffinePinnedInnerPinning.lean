import Langlands.GroupScheme.Reductive.AffinePinnedTestCentrality

/-! # Pinning equations for actual relative inner representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M : AffinePinnedModel.{u}} {T : Scheme.{u}} (f : T ⟶ M.base)
  (A : Type u) [CommRing A] [Algebra M.ring A]
  (a : Spec (CommRingCat.of A) ⟶ T)
  (ha : algebraBaseMap M.ring A = a ≫ f)

/-- Identify an actual affine test with the same test viewed over the
original coefficient base. -/
def coefficientTestIso :
    (algSpec (CommRingCat.of M.ring)).obj
        (op (CommAlgCat.of (CommRingCat.of M.ring) A)) ≅
      (Over.map f).obj (Over.mk a) :=
  Over.isoMk (Iso.refl _) (by simpa using ha.symm)

/-- Multiplicative projection of relative points to the original affine
group on the actual coefficient test. -/
def coefficientTestPointsEquiv (G : GroupScheme M.base) :
    (Over.mk a ⟶ ((baseChange f).obj G).X) ≃* Lie.AffinePoints G A :=
  (baseChangePointsEquiv f G (Over.mk a)).trans
    { toFun := fun x => (coefficientTestIso f A a ha).hom ≫ x
      invFun := fun x => (coefficientTestIso f A a ha).inv ≫ x
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }

@[simp]
theorem coefficientTestPointsEquiv_left (G : GroupScheme M.base)
    (x : Over.mk a ⟶ ((baseChange f).obj G).X) :
    (coefficientTestPointsEquiv f A a ha G x).left =
      x.left ≫ pullback.fst G.X.hom f := by
  change 𝟙 _ ≫ (x.left ≫ _) = _
  exact Category.id_comp _

theorem coefficientTestPointsEquiv_torus
    (t : Over.mk a ⟶ (splitTorus T M.coordinates).X) :
    coefficientTestPointsEquiv f A a ha M.group
        (t ≫ (M.inclusionOver f).hom.hom) =
      coefficientTestPointsEquiv f A a ha (splitTorus M.base M.coordinates)
          (t ≫ (splitTorus.baseChangeIso f M.coordinates).inv.hom.hom) ≫
        M.inclusion.hom.hom := by
  change (coefficientTestIso f A a ha).hom ≫
      baseChangePointsEquiv f M.group (Over.mk a)
        (t ≫ (M.inclusionOver f).hom.hom) =
    ((coefficientTestIso f A a ha).hom ≫
      baseChangePointsEquiv f (splitTorus M.base M.coordinates) (Over.mk a)
        (t ≫ (splitTorus.baseChangeIso f M.coordinates).inv.hom.hom)) ≫
      M.inclusion.hom.hom
  change (coefficientTestIso f A a ha).hom ≫
      baseChangePointsEquiv f M.group (Over.mk a)
        (t ≫ ((splitTorus.baseChangeIso f M.coordinates).inv ≫
          (baseChange f).map M.inclusion).hom.hom) = _
  simp only [Grp.comp_hom_hom, Category.assoc]
  rw [← Category.assoc t, baseChangePointsEquiv_comp]

include ha in
/-- The coefficient identity for the dual-number refinement. -/
theorem dualNumber_test_base :
    algebraBaseMap M.ring (DualNumber A) =
      (algebraBaseMap A (DualNumber A) ≫ a) ≫ f := by
  rw [Category.assoc, ← ha]
  simp only [algebraBaseMap, ← Spec.map_comp]
  congr 1

theorem coefficientTestPointsEquiv_constant (G : GroupScheme M.base)
    (x : Over.mk a ⟶ ((baseChange f).obj G).X) :
    coefficientTestPointsEquiv f (DualNumber A)
        (algebraBaseMap A (DualNumber A) ≫ a) (dualNumber_test_base f A a ha) G
        (Over.homMk (V := Over.mk a) (algebraBaseMap A (DualNumber A))
          (by rfl) ≫ x) =
      Lie.constant G (coefficientTestPointsEquiv f A a ha G x) := by
  apply Over.OverMorphism.ext
  simp only [coefficientTestPointsEquiv_left, Over.comp_left,
    Lie.constant, Lie.affineMap_apply]
  exact Category.assoc _ _ _

theorem coefficientTestPointsEquiv_rootVector (s : M.basis.support) :
    coefficientTestPointsEquiv f (DualNumber A)
        (algebraBaseMap A (DualNumber A) ≫ a) (dualNumber_test_base f A a ha) M.group
        (Over.homMk (V := (M.groupOver f).X) (M.rootVectorPoint f A a ha s)
          (M.rootVectorPoint_snd f A a ha s)) =
      (M.rootVectorAt A s).val := by
  apply Over.OverMorphism.ext
  simp only [coefficientTestPointsEquiv_left]
  exact M.rootVectorPoint_fst f A a ha s

/-- Pinning preservation of an actual inner representative gives the adjoint
permutation equation on each local coefficient test. -/
theorem torusPermutesSimpleVectorsAt_of_representsIso
    [IsLocalRing A] (e : Comparison f f) (he : PreservesLocalPinning e)
    (t : Over.mk a ⟶ (splitTorus T M.coordinates).X)
    (ht : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso e
      (t ≫ (M.inclusionOver f).hom.hom)) :
    M.TorusPermutesSimpleVectorsAt A
      (coefficientTestPointsEquiv f A a ha (splitTorus M.base M.coordinates)
        (t ≫ (splitTorus.baseChangeIso f M.coordinates).inv.hom.hom)) := by
  obtain ⟨σ, hσ⟩ := he A a ha ha
  refine ⟨σ, fun s => ?_⟩
  let r : Over.mk (algebraBaseMap A (DualNumber A) ≫ a) ⟶ Over.mk a :=
    Over.homMk (algebraBaseMap A (DualNumber A)) rfl
  let v (s : M.basis.support) :
      Over.mk (algebraBaseMap A (DualNumber A) ≫ a) ⟶ (M.groupOver f).X :=
    Over.homMk (M.rootVectorPoint f A a ha s)
      (M.rootVectorPoint_snd f A a ha s)
  have hpin : v s ≫ e.hom.hom.hom = v (σ s) :=
    Over.OverMorphism.ext (hσ s)
  have hinner := ht r (v s)
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id, hpin] at hinner
  have hp := congrArg
    (coefficientTestPointsEquiv f (DualNumber A)
      (algebraBaseMap A (DualNumber A) ≫ a) (dualNumber_test_base f A a ha) M.group)
    hinner
  dsimp only [r, v] at hp
  simp only [map_mul, map_inv, coefficientTestPointsEquiv_rootVector] at hp
  rw [coefficientTestPointsEquiv_constant f A a ha M.group
    (t ≫ (M.inclusionOver f).hom.hom)] at hp
  rw [coefficientTestPointsEquiv_torus] at hp
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

/-- A torus representative of a pinning-preserving automorphism projects to a
point in the full centre on every nontrivial local coefficient test. -/
theorem mem_center_coefficientTest_of_representsIso
    [IsLocalRing A] (e : Comparison f f)
    (he : PreservesLocalPinning e)
    (t : Over.mk a ⟶ (splitTorus T M.coordinates).X)
    (ht : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso e
      (t ≫ (M.inclusionOver f).hom.hom)) :
    coefficientTestPointsEquiv f A a ha M.group
      (t ≫ (M.inclusionOver f).hom.hom) ∈ (center M.group).carrier
        ((algSpec (CommRingCat.of M.ring)).obj
          (op (CommAlgCat.of (CommRingCat.of M.ring) A))) := by
  rw [coefficientTestPointsEquiv_torus]
  exact M.mem_center_of_torusPermutesSimpleVectorsAt A
    (torusPermutesSimpleVectorsAt_of_representsIso f A a ha e he t ht)

end Langlands.GroupScheme.AffinePinnedModel
