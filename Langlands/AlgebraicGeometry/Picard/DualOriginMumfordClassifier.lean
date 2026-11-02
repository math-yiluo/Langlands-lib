import Langlands.AlgebraicGeometry.Picard.PicardOriginMumfordClassifier
import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement

/-! # The Mumford classifier into the chosen dual over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.DualOriginDimension

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules PicardOriginDimension

variable (mumford : MumfordBundlePicardZeroStatement.{u})
  (k : Type u) [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))
  (hA : HasDualScheme A)

/-- The Picard-zero class of the Mumford family of `L`; it is Picard-zero by the supplied
Mumford statement. -/
def mumfordClass (L : LineBundle A.X.left) : PicardZeroClasses A A.X :=
  ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) (family k A L),
    mumford pullbackTensorComparisonIsIso _ A (unitRigidified k A L) (inverse L)
      (inverseEvaluation L)⟩

/-- The morphism `A → A^∨` to the chosen dual classifying the Mumford family of `L`. -/
def dualClassifier (L : LineBundle A.X.left) : A.X ⟶ dualScheme A hA :=
  dualClassify A hA A.X (mumfordClass mumford k A L)

/-- The classifier sends the unit section to the origin of the dual. -/
lemma one_comp_dualClassifier (L : LineBundle A.X.left) :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) ≫ dualClassifier mumford k A hA L =
      dualOrigin A hA := by
  rw [dualClassifier, ← dualClassify_pullback A
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence picardZeroPullback hA, dualOrigin]
  congr 1
  apply Subtype.ext
  exact Quotient.sound ⟨mumfordZeroParameterIso A pullbackTensorComparisonIsIso
    (unitRigidified k A L) (inverse L) (inverseEvaluation L) _⟩

/-- The classifier sends the rational origin of `A` to the rational origin of the dual. -/
lemma dualClassifier_unit (L : LineBundle A.X.left) :
    (dualClassifier mumford k A hA L).left (unitSection A (IsLocalRing.closedPoint k)) =
      (dualOrigin A hA).left (IsLocalRing.closedPoint k) := by
  have h := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k))
    (one_comp_dualClassifier mumford k A hA L)
  simp only [Over.comp_left] at h
  exact h

/-- A rational point sent by the classifier to the origin of the dual pulls the Mumford
family back to the trivial family. -/
lemma nonempty_pullback_iso_trivial (L : LineBundle A.X.left)
    (σ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (hσ : σ ≫ dualClassifier mumford k A hA L = dualOrigin A hA) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) σ).obj (family k A L) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) := by
  have h := dualClassify_spec A hA _
    (picardZeroClassesPullback picardZeroPullback A σ (mumfordClass mumford k A L))
  rw [dualClassify_pullback A Langlands.SchemeModule.RigidifiedModule.pullbackCoherence
    picardZeroPullback hA, ← dualClassifier, hσ, dualOrigin_spec] at h
  exact Quotient.exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If the Mumford family of `L` pulls back to the trivial family along a rational section,
then the translation by that section preserves `L` up to isomorphism. -/
lemma translation_iso_of_pullback_iso_trivial (L : LineBundle A.X.left)
    (σ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (e₁ : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) σ).obj (family k A L) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp σ).left).obj L ≅ L) := by
  let S := Spec (CommRingCat.of k)
  -- the underlying module isomorphism with the structure sheaf
  let c₀ := (Langlands.SchemeModule.RigidifiedModule.forget _).mapIso
    ((RigidifiedLineBundle.forgetToRigidified _).mapIso e₁)
  let x := GroupScheme.baseChangeSection (𝟙 S) A.toGrp σ
  let sy := pullbackSymmetry (𝟙 S) A.X.hom
  let i := pullback.fst A.X.hom (𝟙 S)
  let t := (GroupScheme.translation ((baseChange (𝟙 S)).obj A).toGrp x).left
  let E := tensorObj ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback i).obj L.obj))
    ((Scheme.Modules.pullback i).obj (inverse L).obj)
  let premise : (Scheme.Modules.pullback sy.inv).obj ((Scheme.Modules.pullback sy.hom).obj E) ≅
      E :=
    (Scheme.Modules.pullbackComp sy.inv sy.hom).app E ≪≫
      (Scheme.Modules.pullbackCongr sy.inv_hom_id).app E ≪≫ (Scheme.Modules.pullbackId _).app E
  let c := FieldMumfordPoint.carrierIso A σ pullbackTensorComparisonIsIso x
    (baseChangeSection_left_fst k A σ) L.obj (inverse L).obj
    ((Scheme.Modules.pullback sy.hom).obj E)
    (fieldLineBundleTriviality k ((LineBundle.pullback σ.left).obj (inverse L))).some
    premise.symm
  let eE : E ≅ structureSheaf _ :=
    premise.symm ≪≫ (Scheme.Modules.pullback sy.inv).mapIso (c.symm ≪≫ c₀) ≪≫
      pullbackUnitIso sy.inv
  obtain ⟨e₂⟩ := TranslationOfSmoothFamily.pullback_iso_of_tensor_trivial
    pullbackTensorComparisonIsIso i t L (inverse L) (inverseEvaluation L) (Iso.refl _) eE
  exact ⟨LineBundle.isoOfPullbackIso i
    (GroupScheme.fibreTranslationIso (𝟙 S) A.toGrp σ L ≪≫ e₂)⟩

/-- A rational section sent by the classifier to the origin of the dual stabilizes `L`. -/
lemma translation_iso_of_comp_dualClassifier (L : LineBundle A.X.left)
    (σ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (hσ : σ ≫ dualClassifier mumford k A hA L = dualOrigin A hA) :
    Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp σ).left).obj L ≅ L) :=
  translation_iso_of_pullback_iso_trivial k A L σ
    (nonempty_pullback_iso_trivial mumford k A hA L σ hσ).some

/-- The classifier is locally of finite type when the dual is. -/
lemma locallyOfFiniteType_dualClassifier [LocallyOfFiniteType (dualScheme A hA).hom]
    (L : LineBundle A.X.left) :
    LocallyOfFiniteType (dualClassifier mumford k A hA L).left := by
  have : LocallyOfFiniteType ((dualClassifier mumford k A hA L).left ≫ (dualScheme A hA).hom) := by
    rw [Over.w]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (dualScheme A hA).hom

variable [IsAlgClosed k]

/-- The rational origin of a locally finite type dual is a closed point. -/
lemma isClosed_dualOrigin [LocallyOfFiniteType (dualScheme A hA).hom] :
    IsClosed ({(dualOrigin A hA).left (IsLocalRing.closedPoint k)} :
      Set (dualScheme A hA).left) :=
  ((pointEquivClosedPoint (dualScheme A hA).hom) ⟨(dualOrigin A hA).left, Over.w _⟩).2

/-- If only finitely many rational translations preserve `L`, the fibre of the classifier
through the origin of the dual is a finite set of closed points. -/
lemma dualFiber_finite_and_closed [LocallyOfFiniteType (dualScheme A hA).hom]
    (L : LineBundle A.X.left)
    (hfin : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}) :
    ((dualClassifier mumford k A hA L).left ⁻¹'
        {(dualOrigin A hA).left (IsLocalRing.closedPoint k)}).Finite ∧
      ∀ z ∈ (dualClassifier mumford k A hA L).left ⁻¹'
          {(dualOrigin A hA).left (IsLocalRing.closedPoint k)},
        IsClosed ({z} : Set A.X.left) := by
  set f := (dualClassifier mumford k A hA L).left
  set Z := f ⁻¹' {(dualOrigin A hA).left (IsLocalRing.closedPoint k)}
  have hZ : IsClosed Z := (isClosed_dualOrigin k A hA).preimage f.continuous
  let φ : (Z ∩ closedPoints A.X.left : Set A.X.left) →
      {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
        Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} :=
    fun z ↦ ⟨Over.homMk (pointOfClosedPoint A.X.hom z.1 z.2.2)
        (pointOfClosedPoint_comp A.X.hom z.1 z.2.2),
      translation_iso_of_comp_dualClassifier mumford k A hA L _ (by
        apply Over.OverMorphism.ext
        apply ext_of_apply_closedPoint_eq (dualScheme A hA).hom (Over.w _) (Over.w _)
        exact (congrArg f (pointOfClosedPoint_apply A.X.hom z.1 z.2.2 _)).trans z.2.1)⟩
  have hinj : Function.Injective φ := by
    intro z₁ z₂ h
    have h' := congrArg (fun s ↦ s.1.left (IsLocalRing.closedPoint k)) h
    simp only [φ, Over.homMk_left] at h'
    exact Subtype.ext ((pointOfClosedPoint_apply A.X.hom z₁.1 z₁.2.2 _).symm.trans
      (h'.trans (pointOfClosedPoint_apply A.X.hom z₂.1 z₂.2.2 _)))
  have hcpfin : (Z ∩ closedPoints A.X.left).Finite :=
    Set.finite_coe_iff.mp (Finite.of_injective φ hinj)
  have hcpcl : IsClosed (Z ∩ closedPoints A.X.left) := by
    simpa only [Set.biUnion_of_singleton] using
      hcpfin.isClosed_biUnion (fun z hz ↦ hz.2)
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  have hEq : Z ∩ closedPoints A.X.left = Z := by
    have h := JacobsonSpace.closure_inter_closedPoints_eq_closure hZ.isLocallyClosed
    rwa [hcpcl.closure_eq, hZ.closure_eq] at h
  exact ⟨hEq ▸ hcpfin, fun z hz ↦ (hEq.symm ▸ hz : z ∈ Z ∩ closedPoints A.X.left).2⟩

/-- Under the finite-stabilizer premise the classifier is quasi-finite at the unit. -/
lemma quasiFiniteAt_dualClassifier [LocallyOfFiniteType (dualScheme A hA).hom]
    (L : LineBundle A.X.left)
    (hfin : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}) :
    (dualClassifier mumford k A hA L).left.QuasiFiniteAt
      (unitSection A (IsLocalRing.closedPoint k)) := by
  have := locallyOfFiniteType_dualClassifier mumford k A hA L
  obtain ⟨h₁, h₂⟩ := dualFiber_finite_and_closed mumford k A hA L hfin
  rw [← dualClassifier_unit mumford k A hA L] at h₁ h₂
  exact quasiFiniteAt_of_finite_fiber _ _ h₁ h₂

end Langlands.AbelianScheme.DualOriginDimension

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard DualOriginDimension

/-- Let `K` be algebraically closed. Assume that the Mumford family is Picard-zero, that
chosen duals are locally of finite presentation, and that ample line bundles exist on
abelian varieties over algebraically closed fields. Then the stalk of the chosen dual of an
abelian variety of dimension `g` at its rational origin has Krull dimension at least `g`. -/
theorem algClosedFieldDualOriginDimensionLowerBound_of
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ)
    (hg : A.HasRelativeDimension g) :
    (g : WithBot ℕ∞) ≤ ringKrullDim ((dualScheme A hA).left.presheaf.stalk
      ((dualOrigin A hA).left (IsLocalRing.closedPoint K))) := by
  have : LocallyOfFinitePresentation (dualScheme A hA).hom :=
    finitePresentation (Spec (CommRingCat.of K)) A hA
  obtain ⟨L, hL⟩ := ample K A.toGrp inferInstance inferInstance inferInstance
  have hfin := algClosedFieldAmpleTranslationStabilizerFinite K A L hL
  rw [← fieldSmoothClosedPointStalkDimension K A.X.left A.X.hom g hg _
    (PicardOriginDimension.isClosed_unit K A), ← dualClassifier_unit mumford K A hA L]
  exact quasiFiniteAtStalkDimension _ _ _ (locallyOfFiniteType_dualClassifier mumford K A hA L) _
    (quasiFiniteAt_dualClassifier mumford K A hA L hfin)

end Langlands.AbelianScheme
