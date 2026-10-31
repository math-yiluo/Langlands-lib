import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvarianceOfSmoothFamily
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionStatement
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Fiber

/-! # The Mumford classifier into a universal rigidified Picard parameter over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.PicardOriginDimension

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (k : Type u) [Field k]
  (A : AbelianScheme (Spec (CommRingCat.of k)))

/-- Over a field, the restriction of a line bundle to the unit section is trivial; this
rigidifies the actual line bundle along the unit section. -/
def unitRigidified (L : LineBundle A.X.left) : RigidifiedLineBundle (unitSection A) :=
  RigidifiedLineBundle.ofLineBundle L
    (fieldLineBundleTriviality k ((LineBundle.pullback (unitSection A)).obj L)).some.symm

/-- A chosen tensor inverse of an actual line bundle. -/
def inverse {X : Scheme.{u}} (L : LineBundle X) : LineBundle X :=
  (LineBundle.exists_tensorObj_iso_structureSheaf L).choose

/-- The evaluation isomorphism of the chosen tensor inverse. -/
def inverseEvaluation {X : Scheme.{u}} (L : LineBundle X) :
    tensorObj L.obj (inverse L).obj ≅ structureSheaf X :=
  (LineBundle.exists_tensorObj_iso_structureSheaf L).choose_spec.some

/-- The actual rigidified Mumford family of `L`, parametrized by `A` itself. -/
def family (L : LineBundle A.X.left) : RigidifiedFamily A A.X :=
  mumfordBundle A pullbackTensorComparisonIsIso (unitRigidified k A L) (inverse L)
    (inverseEvaluation L)

variable {P : Over (Spec (CommRingCat.of k))} (U : RigidifiedFamily A P)
  (hU : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) U)

/-- The morphism `A → P` classifying the Mumford family of `L`. -/
def classifier (L : LineBundle A.X.left) : A.X ⟶ P :=
  RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) U hU
    (family k A L)

/-- The classifier sends the unit section to the section classifying the trivial family. -/
lemma one_comp_classifier (L : LineBundle A.X.left) :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) ≫ classifier k A U hU L =
      RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) U hU := by
  rw [classifier, ← RigidifiedLineBundle.classifyFamily_pullback]
  refine (RigidifiedLineBundle.classifyFamily_eq_of_iso A.X.hom (unitSection A)
    (unitSection_comp A) U hU (mumfordZeroParameterIso A pullbackTensorComparisonIsIso
      (unitRigidified k A L) (inverse L) (inverseEvaluation L) _)).trans ?_
  rw [RigidifiedLineBundle.classifyFamily_trivial,
    Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from _) (𝟙 _), Category.id_comp]

/-- The classifier sends the rational origin of `A` to the published origin point of `P`. -/
lemma classifier_unit (L : LineBundle A.X.left) :
    (classifier k A U hU L).left (unitSection A (IsLocalRing.closedPoint k)) =
      fullPicardOriginPoint k A U hU := by
  have h := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) (one_comp_classifier k A U hU L)
  simp only [Over.comp_left] at h
  exact h

/-- A rational section is a lift through `𝟙` of its restricted section. -/
lemma baseChangeSection_left_fst (σ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) :
    (GroupScheme.baseChangeSection (𝟙 _) A.toGrp σ).left ≫
        pullback.fst A.X.hom (𝟙 (Spec (CommRingCat.of k))) = σ.left := by
  have h := congrArg Over.Hom.left
    ((GroupScheme.baseChangePointsEquiv (𝟙 (Spec (CommRingCat.of k))) A.toGrp
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).apply_symm_apply
        (Over.mkIdTerminal.from _ ≫ σ))
  exact h.trans (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If a rational section is sent by the classifier to the trivial parameter, then the
translation by that section preserves `L` up to isomorphism. -/
lemma translation_iso_of_comp_classifier (L : LineBundle A.X.left)
    (σ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (hσ : σ ≫ classifier k A U hU L =
      RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) U hU) :
    Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp σ).left).obj L ≅ L) := by
  let S := Spec (CommRingCat.of k)
  have hclass : RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A)
        (unitSection_comp A) U hU
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) σ).obj (family k A L)) =
      RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) U hU
        (RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
          (Over.mk (𝟙 S))) := by
    rw [RigidifiedLineBundle.classifyFamily_pullback, RigidifiedLineBundle.classifyFamily_trivial,
      Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from _) (𝟙 _), Category.id_comp]
    exact hσ
  let e₁ := RigidifiedLineBundle.isoOfClassifyFamilyEq A.X.hom (unitSection A)
    (unitSection_comp A) U hU _ _ hclass
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

/-- A locally finite type morphism is quasi-finite at a point whose fibre is a finite set of
closed points. -/
lemma quasiFiniteAt_of_finite_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hfin : (f ⁻¹' {f x}).Finite)
    (hcl : ∀ z ∈ f ⁻¹' {f x}, IsClosed ({z} : Set X)) :
    f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber,
    ← (f.fiberHomeo (f x)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [← isClosed_compl_iff]
  have hc : IsClosed (⋃ z ∈ f ⁻¹' {f x} \ {x}, ({z} : Set X)) :=
    (hfin.subset Set.sdiff_subset).isClosed_biUnion (fun z hz ↦ hcl z hz.1)
  convert hc.preimage continuous_subtype_val using 1
  ext ⟨z, hz⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage,
    Set.mem_iUnion, Set.mem_sdiff, exists_prop]
  exact ⟨fun h ↦ ⟨z, ⟨hz, fun e ↦ h (Subtype.ext e)⟩, rfl⟩,
    fun ⟨w, ⟨_, hw⟩, hzw⟩ e ↦ hw (hzw ▸ congrArg Subtype.val e)⟩

variable [IsAlgClosed k]

/-- The published origin point of a locally finite type parameter is closed. -/
lemma isClosed_origin [LocallyOfFiniteType P.hom] :
    IsClosed ({fullPicardOriginPoint k A U hU} : Set P.left) :=
  ((pointEquivClosedPoint P.hom)
    ⟨(RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A)
      U hU).left, Over.w _⟩).2

/-- The rational origin of `A` is a closed point. -/
lemma isClosed_unit :
    IsClosed ({unitSection A (IsLocalRing.closedPoint k)} : Set A.X.left) :=
  ((pointEquivClosedPoint A.X.hom) ⟨unitSection A, unitSection_comp A⟩).2

/-- If only finitely many rational translations preserve `L`, the fibre of the classifier
through the origin is a finite set of closed points. -/
lemma fiber_finite_and_closed [LocallyOfFiniteType P.hom] (L : LineBundle A.X.left)
    (hfin : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}) :
    ((classifier k A U hU L).left ⁻¹' {fullPicardOriginPoint k A U hU}).Finite ∧
      ∀ z ∈ (classifier k A U hU L).left ⁻¹' {fullPicardOriginPoint k A U hU},
        IsClosed ({z} : Set A.X.left) := by
  set f := (classifier k A U hU L).left
  set Z := f ⁻¹' {fullPicardOriginPoint k A U hU}
  have hZ : IsClosed Z := (isClosed_origin k A U hU).preimage f.continuous
  let φ : (Z ∩ closedPoints A.X.left : Set A.X.left) →
      {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
        Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} :=
    fun z ↦ ⟨Over.homMk (pointOfClosedPoint A.X.hom z.1 z.2.2)
        (pointOfClosedPoint_comp A.X.hom z.1 z.2.2),
      translation_iso_of_comp_classifier k A U hU L _ (by
        apply Over.OverMorphism.ext
        apply ext_of_apply_closedPoint_eq P.hom (Over.w _) (Over.w _)
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

omit [IsAlgClosed k] in
/-- The classifier is locally of finite type when the parameter is. -/
lemma locallyOfFiniteType_classifier [LocallyOfFiniteType P.hom] (L : LineBundle A.X.left) :
    LocallyOfFiniteType (classifier k A U hU L).left := by
  have : LocallyOfFiniteType ((classifier k A U hU L).left ≫ P.hom) := by
    rw [Over.w]
    infer_instance
  exact locallyOfFiniteType_of_comp _ P.hom

/-- Under the finite-stabilizer premise the classifier is quasi-finite at the origin. -/
lemma quasiFiniteAt_classifier [LocallyOfFiniteType P.hom] (L : LineBundle A.X.left)
    (hfin : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}) :
    (classifier k A U hU L).left.QuasiFiniteAt (unitSection A (IsLocalRing.closedPoint k)) := by
  have := locallyOfFiniteType_classifier k A U hU L
  obtain ⟨h₁, h₂⟩ := fiber_finite_and_closed k A U hU L hfin
  rw [← classifier_unit k A U hU L] at h₁ h₂
  exact quasiFiniteAt_of_finite_fiber _ _ h₁ h₂

end Langlands.AbelianScheme.PicardOriginDimension

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard PicardOriginDimension

/-- The origin local-dimension bound, from the quasi-finite stalk inequality and the stalk
dimension at a closed point of a smooth scheme over a field. -/
theorem algClosedFieldRigidifiedPicardOriginDimensionLowerBound_of_stalkDimension
    (hq : QuasiFiniteAtStalkDimensionStatement.{u})
    (hs : FieldSmoothClosedPointStalkDimensionStatement.{u}) :
    AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u} := by
  intro k _ _ A P U hU g hP hA L hfin
  rw [← hs k A.X.left A.X.hom g hA _ (isClosed_unit k A), ← classifier_unit k A U hU L]
  exact hq _ _ _ (locallyOfFiniteType_classifier k A U hU L) _
    (quasiFiniteAt_classifier k A U hU L hfin)

end Langlands.AbelianScheme
