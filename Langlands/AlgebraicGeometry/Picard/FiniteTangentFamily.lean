import Langlands.AlgebraicGeometry.Deformation.ArtinianFiniteTangents
import Langlands.AlgebraicGeometry.Picard.ArtinianDualNumberComparison

/-! # Actual finite simultaneous first-order Picard families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTangentFamily

open Langlands.AlgebraicGeometry.Deformation

local notation "preservation" =>
  Langlands.Scheme.Modules.pullbackTensorComparisonIsIso

open ArtinianTest

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- Ordinary classes of actual line bundles on an actual Artinian test. -/
abbrev OrdinaryClasses (A : ArtinianTest k K) :=
  LineBundle.IsoClasses preservation ((relativeSpace f).obj (ArtinianTest.base A))

/-- Ordinary pullback along the actual map of relative test schemes. -/
def restrictHom {A B : ArtinianTest k K} (q : A ⟶ B) :
    OrdinaryClasses f A →* OrdinaryClasses f B :=
  LineBundle.pullbackHom preservation ((relativeSpace f).map (ArtinianTest.baseMap q))

lemma restrictHom_comp {A B C : ArtinianTest k K} (q : A ⟶ B) (r : B ⟶ C)
    (x : OrdinaryClasses f A) :
    restrictHom f r (restrictHom f q x) = restrictHom f (q ≫ r) x := by
  apply LineBundle.pullbackHom_comp_eq preservation
    ((relativeSpace f).map (ArtinianTest.baseMap r))
    ((relativeSpace f).map (ArtinianTest.baseMap q)) _ x
  rw [← (relativeSpace f).map_comp, ArtinianTest.baseMap_comp]

@[simp]
lemma restrictHom_id (A : ArtinianTest k K) (x : OrdinaryClasses f A) :
    restrictHom f (𝟙 A) x = x := by
  change LineBundle.pullbackHom preservation
    ((relativeSpace f).map (ArtinianTest.baseMap (𝟙 A))) x = x
  rw [ArtinianTest.baseMap_id, (relativeSpace f).map_id]
  exact LineBundle.pullbackHom_id preservation x

/-- Forget the specified residue identification on pointed isomorphism classes. -/
def forgetClass {A : ArtinianTest k K} :
    Quotient (isIsomorphicSetoid (ArtinianTestDeformations.Deformations f M A)) →
      OrdinaryClasses f A :=
  Quotient.lift (fun L ↦ LineBundle.isoClass preservation L.right.of)
    (fun _ _ ⟨e⟩ ↦ LineBundle.isoClass_eq_of_iso e.hom.right.iso)

@[simp]
lemma forgetClass_mk {A : ArtinianTest k K}
    (L : ArtinianTestDeformations.Deformations f M A) :
    forgetClass f M (Quotient.mk _ L) =
      LineBundle.isoClass preservation L.right.of := rfl

/-- Restriction on pointed classes uses the original actual restriction functor. -/
def restrictClass {A B : ArtinianTest k K} (q : A ⟶ B) :
    Quotient (isIsomorphicSetoid (ArtinianTestDeformations.Deformations f M A)) →
      Quotient (isIsomorphicSetoid (ArtinianTestDeformations.Deformations f M B)) :=
  Quotient.map (ArtinianTestDeformations.restrict f M q).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(ArtinianTestDeformations.restrict f M q).mapIso e⟩)

lemma forgetClass_restrict {A B : ArtinianTest k K} (q : A ⟶ B)
    (x : Quotient (isIsomorphicSetoid
      (ArtinianTestDeformations.Deformations f M A))) :
    forgetClass f M (restrictClass f M q x) =
      restrictHom f q (forgetClass f M x) := by
  induction x using Quotient.inductionOn with | h L => rfl

lemma forgetClass_reduction {A : ArtinianTest k K}
    (x : Quotient (isIsomorphicSetoid
      (ArtinianTestDeformations.Deformations f M A))) :
    LineBundle.pullbackHom preservation
      ((relativeSpace f).map (ArtinianTest.reduction A)) (forgetClass f M x) =
        LineBundle.isoClass preservation M := by
  induction x using Quotient.inductionOn with | h L => ?_
  exact LineBundle.isoClass_eq_of_iso (ArtinianTestDeformations.reductionIso f M L).symm

/-- Any ordinary class with the required reduction has an actual pointed representative. -/
lemma exists_deformation_of_class (A : ArtinianTest k K) (x : OrdinaryClasses f A)
    (hx : LineBundle.pullbackHom preservation
      ((relativeSpace f).map (ArtinianTest.reduction A)) x =
        LineBundle.isoClass preservation M) :
    ∃ L : ArtinianTestDeformations.Deformations f M A,
      LineBundle.isoClass preservation L.right.of = x := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep x
  change LineBundle.isoClass preservation L = x at hL
  have he : LineBundle.isoClass preservation
      ((LineBundle.pullback ((relativeSpace f).map
        (ArtinianTest.reduction A))).obj L) = LineBundle.isoClass preservation M := by
    change LineBundle.pullbackHom preservation _ (LineBundle.isoClass preservation L) = _
    rw [hL]
    exact hx
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp he
  exact ⟨ArtinianTestDeformations.mk f M A L e.symm, hL⟩

private lemma comparison_forget (x : ArtinianDualNumberComparison.Classes f M) :
    (DualNumberThickening.pointedClassEquiv (ArtinianDualNumberComparison.residueStructure (K := K) f) M
      preservation (ArtinianDualNumberComparison.classEquiv f M x)).val =
        LineBundle.pullbackHom preservation (ArtinianDualNumberComparison.spaceIso (K := K) f).hom
          (forgetClass f M x) := by
  induction x using Quotient.inductionOn with | h L => rfl

/-- For the actual dual-number target, forgetting reduction is injective on classes. -/
lemma forgetClass_dual_injective :
    Function.Injective (forgetClass f M (A := ArtinianTest.dualNumbers k K)) := by
  intro x y h
  apply (ArtinianDualNumberComparison.classEquiv f M).injective
  apply (DualNumberThickening.pointedClassEquiv
    (ArtinianDualNumberComparison.residueStructure (K := K) f) M preservation).injective
  apply Subtype.ext
  simpa only [comparison_forget] using
    congrArg (LineBundle.pullbackHom preservation (ArtinianDualNumberComparison.spaceIso (K := K) f).hom) h

/-- The ordinary constant dual-number lift. -/
def dualSplit : OrdinaryClasses f (ArtinianTest.dualNumbers k K) :=
  restrictHom f (ArtinianTest.dualSection k K) (LineBundle.isoClass preservation M)

lemma dualSplit_reduction :
    restrictHom f (ArtinianTest.dualReduction k K) (dualSplit f M) =
      LineBundle.isoClass preservation M := by
  rw [dualSplit, restrictHom_comp, ArtinianTest.dualSection_reduction, restrictHom_id]

/-- The ordinary class of a tangent direction, divided by the constant lift. -/
def normalized (x : ArtinianDualNumberComparison.Classes f M) :
    OrdinaryClasses f (ArtinianTest.dualNumbers k K) :=
  forgetClass f M x / dualSplit f M

lemma normalized_reduction (x : ArtinianDualNumberComparison.Classes f M) :
    restrictHom f (ArtinianTest.dualReduction k K) (normalized f M x) = 1 := by
  rw [normalized, map_div, dualSplit_reduction]
  have h := forgetClass_reduction f M x
  change restrictHom f (ArtinianTest.dualReduction k K) (forgetClass f M x) = _ at h
  rw [h]
  exact div_self' _

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Tensor the normalized directions after their actual coordinate inclusions. -/
def simultaneousClass (v : ι → ArtinianDualNumberComparison.Classes f M) : OrdinaryClasses f (FiniteTangents.test k K ι) :=
  restrictHom f (FiniteTangents.sectionMap k K ι) (LineBundle.isoClass preservation M) *
    ∏ i, restrictHom f (FiniteTangents.includeAxis k K i) (normalized f M (v i))

lemma simultaneousClass_reduction (v : ι → ArtinianDualNumberComparison.Classes f M) :
    restrictHom f (FiniteTangents.reduction k K ι) (simultaneousClass f M v) =
      LineBundle.isoClass preservation M := by
  simp only [simultaneousClass, map_mul, map_prod, restrictHom_comp,
    FiniteTangents.sectionMap_reduction, restrictHom_id, FiniteTangents.includeAxis_reduction,
    normalized_reduction, Finset.prod_const_one, mul_one]

lemma simultaneousClass_axis (v : ι → ArtinianDualNumberComparison.Classes f M) (i : ι) :
    restrictHom f (FiniteTangents.axis k K i) (simultaneousClass f M v) =
      forgetClass f M (v i) := by
  rw [simultaneousClass, map_mul, map_prod, restrictHom_comp, FiniteTangents.sectionMap_axis]
  change dualSplit f M * (∏ j, restrictHom f (FiniteTangents.axis k K i)
    (restrictHom f (FiniteTangents.includeAxis k K j) (normalized f M (v j)))) = _
  have hprod : (∏ j, restrictHom f (FiniteTangents.axis k K i)
      (restrictHom f (FiniteTangents.includeAxis k K j) (normalized f M (v j)))) =
        normalized f M (v i) := by
    rw [Finset.prod_eq_single i]
    · rw [restrictHom_comp, FiniteTangents.includeAxis_axis, ite_eq_left rfl, restrictHom_id]
    · intro j _ hji
      rw [restrictHom_comp, FiniteTangents.includeAxis_axis, ite_eq_right hji,
        ← restrictHom_comp, normalized_reduction, map_one]
    · simp
  rw [hprod, normalized]
  exact mul_div_cancel _ _

/-- The simultaneous class has an actual bundle with a specified residue identification. -/
lemma exists_simultaneous (v : ι → ArtinianDualNumberComparison.Classes f M) :
    ∃ L : ArtinianTestDeformations.Deformations f M (FiniteTangents.test k K ι),
      LineBundle.isoClass preservation L.right.of = simultaneousClass f M v := by
  apply exists_deformation_of_class
  exact simultaneousClass_reduction f M v

/-- A chosen actual simultaneous pointed deformation. -/
def family (v : ι → ArtinianDualNumberComparison.Classes f M) :
    ArtinianTestDeformations.Deformations f M (FiniteTangents.test k K ι) :=
  Classical.choose (exists_simultaneous f M v)

lemma family_class (v : ι → ArtinianDualNumberComparison.Classes f M) :
    LineBundle.isoClass preservation (family f M v).right.of =
      simultaneousClass f M v :=
  Classical.choose_spec (exists_simultaneous f M v)

/-- Each coordinate restriction is the prescribed actual pointed deformation class. -/
theorem family_axis (v : ι → ArtinianDualNumberComparison.Classes f M) (i : ι) :
    Quotient.mk _ ((ArtinianTestDeformations.restrict f M
      (FiniteTangents.axis k K i)).obj (family f M v)) = v i := by
  apply forgetClass_dual_injective f M
  change restrictHom f (FiniteTangents.axis k K i)
    (LineBundle.isoClass preservation (family f M v).right.of) = _
  rw [family_class, simultaneousClass_axis]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTangentFamily
