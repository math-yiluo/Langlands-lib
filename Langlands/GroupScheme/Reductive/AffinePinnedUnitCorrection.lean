import Langlands.GroupScheme.Reductive.AlignedWeightLineUnits
import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Lie.InnerAdjoint

/-! # Unit correction of actual scalar-extended pinning vectors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

private local instance (P : AffinePinnedModel.{u}) (B : Type u)
    [CommRing B] [Algebra P.ring B] :
    IsAffineHom (P.groupOver (algebraBaseMap P.ring B)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd P.group.X.hom (algebraBaseMap P.ring B)))

variable (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
  [Algebra M.ring A] [Algebra N.ring A]
  (τ : splitTorus.commGroupScheme (Spec (CommRingCat.of A)) M.coordinates ≅
    splitTorus.commGroupScheme (Spec (CommRingCat.of A)) N.coordinates)
  (Φ : (M.groupOver (algebraBaseMap M.ring A)) ≅ (N.groupOver (algebraBaseMap N.ring A)))
  (hτ : (M.inclusionOver (algebraBaseMap M.ring A)) ≫ Φ.hom =
    CommGroupScheme.groupHom τ.hom ≫ (N.inclusionOver (algebraBaseMap N.ring A)))
  (σ : M.basis.support ≃ N.basis.support)
  (hχ : ∀ s : M.basis.support,
    characterLattice.congr τ
      (splitTorus.exponentCharacter (Spec (CommRingCat.of A)) M.coordinates
        (M.rootDatum.root s)) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of A)) N.coordinates
        (N.rootDatum.root (σ s)))

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
include hτ hχ in
/-- Actual scalar-extended chosen pinning vectors have unique unit
discrepancies under a supplied torus- and simple-character-aligned comparison. -/
theorem existsUnique_pinning_units :
    ∃! c : M.basis.support → Aˣ, ∀ s : M.basis.support,
      Lie.targetMapLinear Φ.hom A (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
        (c s : A) • (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val := by
  have hu (s : M.basis.support) := splitTorus.existsUnique_unit_smul_of_aligned_weightLines
    τ Φ hτ (M.rootDatum.root s) (N.rootDatum.root (σ s)) (hχ s)
    (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s)) (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)))
  classical
  choose c hc huniq using hu
  exact ⟨c, hc, fun d hd => funext fun s => huniq s (d s) (hd s)⟩

/-- The unique unit discrepancies of the supplied aligned actual pinning
vectors on the common coefficient ring. -/
def pinningUnitDiscrepancies : M.basis.support → Aˣ :=
  (existsUnique_pinning_units M N A τ Φ hτ σ hχ).choose

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem pinningUnitDiscrepancies_spec (s : M.basis.support) :
    Lie.targetMapLinear Φ.hom A
        (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
      (pinningUnitDiscrepancies M N A τ Φ hτ σ hχ s : A) •
        (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val :=
  (existsUnique_pinning_units M N A τ Φ hτ σ hχ).choose_spec.1 s

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- A supplied target torus section with the inverse simple-root values
corrects the chosen actual pinning vectors. -/
theorem correct_pinning_units
    (c : M.basis.support → Aˣ)
    (hc : ∀ s : M.basis.support,
      Lie.targetMapLinear Φ.hom A (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
        (c s : A) • (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
      (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X)
    (ht : ∀ s : M.basis.support, splitTorus.exponentValue N.coordinates
      (splitTorus.algebraPointsEquiv N.coordinates A
        ((splitTorus (Spec (CommRingCat.of A)) N.coordinates).constantPoint t _))
      (Multiplicative.ofAdd (N.rootDatum.root (σ s))) = (c s)⁻¹) :
    ∀ s : M.basis.support,
      Lie.targetMapLinear
        (Φ ≪≫ ((N.groupOver (algebraBaseMap N.ring A)).innerIso
          (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom))).hom A
        (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
          (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val := by
  intro s
  exact splitTorus.targetMapLinear_correct_unit
    (N.inclusionOver (algebraBaseMap N.ring A)) (N.rootDatum.root (σ s)) Φ.hom
    (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val
    (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1) (c s) (hc s) t (ht s)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The corrected differential equation is an equality of the actual
dual-number pinning points of the original models on the coefficient test. -/
theorem correct_rootVectorPoint
    (c : M.basis.support → Aˣ)
    (hc : ∀ s : M.basis.support,
      Lie.targetMapLinear Φ.hom A (M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s) 1).val =
        (c s : A) • (N.scalarWeightTrivialization A (N.rootDatum.root (σ s)) (N.pinning (σ s)) 1).val)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
      (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X)
    (ht : ∀ s : M.basis.support, splitTorus.exponentValue N.coordinates
      (splitTorus.algebraPointsEquiv N.coordinates A
        ((splitTorus (Spec (CommRingCat.of A)) N.coordinates).constantPoint t _))
      (Multiplicative.ofAdd (N.rootDatum.root (σ s))) = (c s)⁻¹)
    (s : M.basis.support) :
    M.rootVectorPoint (algebraBaseMap M.ring A) A (𝟙 _) (by simp) s ≫
      (Φ ≪≫ ((N.groupOver (algebraBaseMap N.ring A)).innerIso
        (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom))).hom.hom.hom.left =
      N.rootVectorPoint (algebraBaseMap N.ring A) A (𝟙 _) (by simp) (σ s) := by
  have hv := correct_pinning_units M N A Φ σ c hc t ht s
  have hp := congrArg (fun X => X.toMul.val.left) hv
  have hpM : ((M.scalarWeightTrivialization A (M.rootDatum.root s)
      (M.pinning s) 1).val.toMul.val).left =
      M.rootVectorPoint (algebraBaseMap M.ring A) A (𝟙 _) (by simp) s :=
    M.scalarExtension_pinning_point A s
  have hpN : ((N.scalarWeightTrivialization A (N.rootDatum.root (σ s))
      (N.pinning (σ s)) 1).val.toMul.val).left =
      N.rootVectorPoint (algebraBaseMap N.ring A) A (𝟙 _) (by simp) (σ s) :=
    N.scalarExtension_pinning_point A (σ s)
  simpa only [lieKernelTargetLinear_val, Over.comp_left, hpM, hpN] using hp

end Langlands.GroupScheme.AffinePinnedModel
