import Langlands.GroupScheme.Reductive.AffinePinnedNormalizedPoints
import Langlands.GroupScheme.Reductive.AffinePinnedUnitCorrection
import Langlands.GroupScheme.Reductive.RelativeSimpleRootLift

/-! # Fppf torus correction of aligned affine comparisons -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

local instance (M : AffinePinnedModel.{u}) (A : Type u)
    [CommRing A] [Algebra M.ring A] :
    IsAffineHom (M.groupOver (algebraBaseMap M.ring A)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring A)))

/-- A section over an arbitrary intermediate scheme, evaluated on an affine test. -/
def affineSectionPoint {A : Type u} [CommRing A] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of A)) (B : Type u) [CommRing B] [Algebra A B]
    (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
    {G : GroupScheme (Spec (CommRingCat.of A))} (t : Over.mk p ⟶ G.X) :
    Lie.AffinePoints G B :=
  Over.homMk (U := (algSpec (CommRingCat.of A)).obj
    (op (CommAlgCat.of (CommRingCat.of A) B))) (V := Over.mk p) a hA.symm ≫ t

variable (M : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra M.ring A]
  {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of A))
  (B : Type u) [CommRing B] [Algebra A B]
  (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)

/-- Constants of a direct section become its actual coefficient-test evaluation. -/
theorem normalized_constant_affineSection
    (z : Over.mk (𝟙 W) ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) :
    normalizedTestPointsEquiv M A p B a hA
      ((M.groupOver (p ≫ algebraBaseMap M.ring A)).constantPoint z (Over.mk a)) =
      affineSectionPoint p B a hA (normalizedBasePointsEquiv M A p z) := by
  apply Over.OverMorphism.ext
  simp only [normalizedTestPointsEquiv_left, constantPoint, Over.comp_left]
  change (a ≫ z.left) ≫ _ ≫ _ = a ≫ (normalizedBasePointsEquiv M A p z).left
  rw [normalizedBasePointsEquiv_left]
  simp only [Category.assoc]

/-- Evaluation of a section commutes with the dual-number constant map. -/
theorem affineSectionPoint_dual
    {G : GroupScheme (Spec (CommRingCat.of A))} (t : Over.mk p ⟶ G.X) :
    affineSectionPoint p (DualNumber B) (algebraBaseMap B (DualNumber B) ≫ a)
      (by
        rw [Category.assoc, ← hA]
        simp only [algebraBaseMap, ← Spec.map_comp]
        rfl) t = Lie.constant G (affineSectionPoint p B a hA t) := by
  apply Over.OverMorphism.ext
  change (algebraBaseMap B (DualNumber B) ≫ a) ≫ t.left =
    algebraBaseMap B (DualNumber B) ≫ (a ≫ t.left)
  exact Category.assoc _ _ _

variable {N : AffinePinnedModel.{u}} [Algebra N.ring A]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- A normalized target torus section corrects every local-test pinning equation
when its actual simple-root values are inverse unit discrepancies. -/
theorem preservesLocalPinning_corrected
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (σ : M.basis.support ≃ N.basis.support) (c : M.basis.support → Aˣ)
    (hc : ∀ s : M.basis.support, Lie.targetMapLinear e.hom A
        (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
      (c s : A) •
        (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val)
    (t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X)
    (ht : ∀ (B : Type u) [CommRing B] [Algebra A B]
      (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
      (s : M.basis.support),
      splitTorus.exponentValue N.coordinates
        (splitTorus.algebraPointsEquiv N.coordinates B (affineSectionPoint p B a hA t))
        (Multiplicative.ofAdd (N.rootDatum.root (σ s))) =
        Units.map (algebraMap A B).toMonoidHom (c s)⁻¹) :
    PreservesLocalPinning
      (pullComparison e p ≪≫ (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso
        ((normalizedBasePointsEquiv N A p).symm
          (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom))) := by
  intro B _ _ _ _ a ha hb
  let : Algebra A B := (Spec.preimage (a ≫ p)).hom.toAlgebra
  have hA : algebraBaseMap A B = a ≫ p := Spec.map_preimage _
  let : IsScalarTower M.ring A B := scalarTower_of_test (a ≫ p) hA
    (by simpa only [Category.assoc] using ha)
  let : IsScalarTower N.ring A B := scalarTower_of_test (a ≫ p) hA
    (by simpa only [Category.assoc] using hb)
  refine ⟨σ, fun s => ?_⟩
  let z := (normalizedBasePointsEquiv N A p).symm
    (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom)
  let v : Over.mk (algebraBaseMap B (DualNumber B) ≫ a) ⟶
      (M.groupOver (p ≫ algebraBaseMap M.ring A)).X :=
    Over.homMk (M.rootVectorPoint _ B a ha s) (M.rootVectorPoint_snd _ _ _ ha s)
  let w : Over.mk (algebraBaseMap B (DualNumber B) ≫ a) ⟶
      (N.groupOver (p ≫ algebraBaseMap N.ring A)).X :=
    Over.homMk (N.rootVectorPoint _ B a hb (σ s)) (N.rootVectorPoint_snd _ _ _ hb (σ s))
  have hd : algebraBaseMap A (DualNumber B) =
      (algebraBaseMap B (DualNumber B) ≫ a) ≫ p := by
    rw [Category.assoc, ← hA]
    simp only [algebraBaseMap, ← Spec.map_comp]
    rfl
  have hconst : normalizedTestPointsEquiv N A p (DualNumber B)
      (algebraBaseMap B (DualNumber B) ≫ a) hd
      ((N.groupOver (p ≫ algebraBaseMap N.ring A)).constantPoint z _) =
      Lie.constant (N.groupOver (algebraBaseMap N.ring A))
        (affineSectionPoint p B a hA t ≫
          (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom) := by
    rw [normalized_constant_affineSection, MulEquiv.apply_symm_apply]
    rw [affineSectionPoint_dual A p B a hA]
    rfl
  have hcoeff := lieKernelTargetLinear_map e.hom (Algebra.ofId A B)
    (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val
  rw [hc s, LinearMap.map_smulₛₗ] at hcoeff
  have hweight := (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).property B
    (splitTorus.algebraPointsEquiv N.coordinates B (affineSectionPoint p B a hA t))
  rw [MulEquiv.symm_apply_apply, ht B a hA s] at hweight
  have hcorrect : adjoint (N.groupOver (algebraBaseMap N.ring A)) B
      (affineSectionPoint p B a hA t ≫
        (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom)
      (Lie.targetMapLinear e.hom B (lieKernelMapLinear
        (M.groupOver (algebraBaseMap M.ring A)) (Algebra.ofId A B)
          (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val)) =
      lieKernelMapLinear (N.groupOver (algebraBaseMap N.ring A)) (Algebra.ofId A B)
        (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val := by
    rw [hcoeff, map_smul, hweight, smul_smul]
    have hunit : (Algebra.ofId A B).toRingHom (c s : A) *
        (Units.map (algebraMap A B).toMonoidHom ((c s)⁻¹) : B) = 1 := by
      change ((Units.map (algebraMap A B).toMonoidHom (c s) : B) *
        (Units.map (algebraMap A B).toMonoidHom ((c s)⁻¹) : B)) = 1
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [hunit, one_smul]
  have hpoint : v ≫
      (pullComparison e p ≪≫ (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso z).hom.hom.hom = w := by
    apply (normalizedTestPointsEquiv N A p (DualNumber B)
      (algebraBaseMap B (DualNumber B) ≫ a) hd).injective
    change normalizedTestPointsEquiv N A p (DualNumber B) _ hd
      ((v ≫ (pullComparison e p).hom.hom.hom) ≫
        ((N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso z).hom.hom.hom) = _
    rw [GroupScheme.comp_innerIso_hom, map_mul, map_mul, map_inv, hconst,
      normalizedTestPointsEquiv_pullComparison (M := M) (N := N) (hA := hd),
      normalizedTestPointsEquiv_rootVector (M := M) (hA := hA),
      normalizedTestPointsEquiv_rootVector (M := N) (hA := hA)]
    exact congrArg (fun X => X.toMul.val) hcorrect
  exact congrArg (fun k => k.left) hpoint

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Inverse actual simple-root values suffice for all-test pinning correction. -/
def AffinePinningCorrectionCriterion : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of A))
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (σ : M.basis.support ≃ N.basis.support) (c : M.basis.support → Aˣ),
    (∀ s : M.basis.support, Lie.targetMapLinear e.hom A
        (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
      (c s : A) •
        (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val) →
    ∀ t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X,
    (∀ (B : Type u) [CommRing B] [Algebra A B]
      (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
      (s : M.basis.support),
      splitTorus.exponentValue N.coordinates
        (splitTorus.algebraPointsEquiv N.coordinates B (affineSectionPoint p B a hA t))
        (Multiplicative.ofAdd (N.rootDatum.root (σ s))) =
        Units.map (algebraMap A B).toMonoidHom (c s)⁻¹) →
    PreservesLocalPinning
      (pullComparison e p ≪≫ (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso
        ((normalizedBasePointsEquiv N A p).symm
          (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom)))

theorem affinePinningCorrectionCriterion : AffinePinningCorrectionCriterion.{u} := by
  intro M N A _ _ _ W p e σ c hc t ht
  exact preservesLocalPinning_corrected M A p e σ c hc t ht

end Langlands.GroupScheme.AffinePinnedModel
