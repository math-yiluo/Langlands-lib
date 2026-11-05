import Langlands.AlgebraicGeometry.Picard.FiniteTangentFamily
import Langlands.AlgebraicGeometry.Picard.RigidifiedDeformationClasses

/-! # Finite first-order Picard families and weighted restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTangentFamily

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest
open DualNumberThickening

local notation "preservation" =>
  Langlands.Scheme.Modules.pullbackTensorComparisonIsIso

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

lemma comparison_forgetClass (x : ArtinianDualNumberComparison.Classes f M) :
    (pointedClassEquiv (ArtinianDualNumberComparison.residueStructure (K := K) f) M
      preservation (ArtinianDualNumberComparison.classEquiv f M x)).val =
        LineBundle.pullbackHom preservation (ArtinianDualNumberComparison.spaceIso (K := K) f).hom
          (forgetClass f M x) := by
  induction x using Quotient.inductionOn with | h L => rfl

/-- The associativity comparison also preserves the actual constant projection. -/
lemma spaceIso_section :
    (ArtinianDualNumberComparison.spaceIso (K := K) f).hom ≫
      (relativeSpace f).map (ArtinianTest.baseMap (ArtinianTest.dualSection k K)) =
        projection (ArtinianDualNumberComparison.residueStructure (K := K) f) := by
  apply pullback.hom_ext
  · simp [relativeSpace, Over.pullback, ArtinianTest.baseMap,
      ArtinianTest.dualSection]
    change structureMap (ArtinianDualNumberComparison.residueStructure (K := K) f) ≫
      dualNumberProjection K =
        projection (ArtinianDualNumberComparison.residueStructure (K := K) f) ≫
          ArtinianDualNumberComparison.residueStructure (K := K) f
    exact pullback.condition.symm
  · simp [relativeSpace, Over.pullback, Category.assoc,
      ArtinianDualNumberComparison.spaceIso_hom_snd]
    rfl

lemma comparison_dualSplit :
    LineBundle.pullbackHom preservation
      (ArtinianDualNumberComparison.spaceIso (K := K) f).hom (dualSplit f M) =
        (splitLiftClass (ArtinianDualNumberComparison.residueStructure (K := K) f) M).val := by
  exact LineBundle.pullbackHom_comp_eq preservation _ _ (spaceIso_section f) _

/-- Normalize the existing comparison of intrinsic actual tangent groups. -/
def comparisonTangentAddEquiv :
    ArtinianDualNumberComparison.Classes f M ≃+
      Additive (DeformationClasses preservation
        (ArtinianDualNumberComparison.residueStructure (K := K) f)) :=
  (ArtinianDualNumberComparison.classAddEquiv f M).trans
    (pointedTangentAddEquiv (ArtinianDualNumberComparison.residueStructure (K := K) f) M)

lemma comparison_normalized (x : ArtinianDualNumberComparison.Classes f M) :
    LineBundle.pullbackHom preservation
      (ArtinianDualNumberComparison.spaceIso (K := K) f).hom (normalized f M x) =
        (comparisonTangentAddEquiv f M x).toMul.val := by
  rw [normalized, map_div, comparison_dualSplit, ← comparison_forgetClass]
  exact div_eq_mul_inv _ _

@[simp]
lemma normalized_zero :
    normalized f M (0 : ArtinianDualNumberComparison.Classes f M) = 1 := by
  apply (LineBundle.classPullbackEquiv preservation
    (ArtinianDualNumberComparison.spaceIso (K := K) f)).injective
  change LineBundle.pullbackHom preservation
      (ArtinianDualNumberComparison.spaceIso (K := K) f).hom (normalized f M 0) =
    LineBundle.pullbackHom preservation
      (ArtinianDualNumberComparison.spaceIso (K := K) f).hom 1
  rw [comparison_normalized, map_zero, map_one]
  rfl

lemma normalized_add (x y : ArtinianDualNumberComparison.Classes f M) :
    normalized f M (x + y) = normalized f M x * normalized f M y := by
  apply (LineBundle.classPullbackEquiv preservation
    (ArtinianDualNumberComparison.spaceIso (K := K) f)).injective
  change LineBundle.pullbackHom preservation _ _ =
    LineBundle.pullbackHom preservation _ _
  rw [map_mul, comparison_normalized, comparison_normalized, comparison_normalized]
  exact congrArg (fun t ↦ t.toMul.val) ((comparisonTangentAddEquiv f M).map_add x y)

/-- Normalization is an additive homomorphism into tensor classes. -/
def normalizedAddHom :
    ArtinianDualNumberComparison.Classes f M →+
      Additive (OrdinaryClasses f (ArtinianTest.dualNumbers k K)) where
  toFun x := Additive.ofMul (normalized f M x)
  map_zero' := normalized_zero f M
  map_add' := normalized_add f M

lemma normalized_sum {ι : Type*} (s : Finset ι)
    (v : ι → ArtinianDualNumberComparison.Classes f M) :
    normalized f M (∑ i ∈ s, v i) = ∏ i ∈ s, normalized f M (v i) := by
  exact congrArg Additive.toMul (map_sum (normalizedAddHom f M) v s)

lemma dualScale_section (c : K) :
    ArtinianTest.dualSection k K ≫ ArtinianTest.dualScale k K c =
      ArtinianTest.dualSection k K := by
  apply ArtinianTest.hom_ext
  rw [ArtinianTest.toAlgHom_comp]
  ext z
  change ArtinianTest.toAlgHom (ArtinianTest.dualScale k K c) (TrivSqZeroExt.inl (z : K)) =
    TrivSqZeroExt.inl z
  apply TrivSqZeroExt.ext
  · exact ArtinianTest.dualScale_fst k K c _
  · rw [ArtinianTest.dualScale_snd]
    change c * 0 = 0
    exact mul_zero _

lemma restrictHom_dualSplit_scale (c : K) :
    restrictHom f (ArtinianTest.dualScale k K c) (dualSplit f M) = dualSplit f M := by
  rw [dualSplit, restrictHom_comp, dualScale_section]

lemma forgetClass_smul (c : K) (x : ArtinianDualNumberComparison.Classes f M) :
    forgetClass f M (c • x) =
      restrictHom f (ArtinianTest.dualScale k K c) (forgetClass f M x) := by
  induction x using Quotient.inductionOn with | h L => rfl

lemma normalized_smul (c : K) (x : ArtinianDualNumberComparison.Classes f M) :
    normalized f M (c • x) =
      restrictHom f (ArtinianTest.dualScale k K c) (normalized f M x) := by
  rw [normalized, forgetClass_smul, normalized, map_div, restrictHom_dualSplit_scale]

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Weighted restriction of the simultaneous class is its actual tangent linear combination. -/
lemma simultaneousClass_weighted (v : ι → ArtinianDualNumberComparison.Classes f M)
    (c : ι → K) :
    restrictHom f (FiniteTangents.weighted k K c) (simultaneousClass f M v) =
      forgetClass f M (∑ i, c i • v i) := by
  rw [simultaneousClass, map_mul, map_prod, restrictHom_comp,
    FiniteTangents.sectionMap_weighted]
  change dualSplit f M * (∏ i, restrictHom f (FiniteTangents.weighted k K c)
    (restrictHom f (FiniteTangents.includeAxis k K i) (normalized f M (v i)))) = _
  simp_rw [restrictHom_comp, FiniteTangents.includeAxis_weighted, ← normalized_smul]
  rw [← normalized_sum f M Finset.univ, normalized]
  exact mul_div_cancel _ _

/-- The weighted restrictions are equal as pointed classes in the actual Artinian fibre. -/
theorem family_weighted (v : ι → ArtinianDualNumberComparison.Classes f M) (c : ι → K) :
    Quotient.mk _ ((ArtinianTestDeformations.restrict f M
      (FiniteTangents.weighted k K c)).obj (family f M v)) = ∑ i, c i • v i := by
  apply forgetClass_dual_injective f M
  change restrictHom f (FiniteTangents.weighted k K c)
    (LineBundle.isoClass preservation (family f M v).right.of) = _
  rw [family_class, simultaneousClass_weighted]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTangentFamily
