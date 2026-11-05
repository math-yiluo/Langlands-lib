import Langlands.AlgebraicGeometry.Deformation.ArtinianDualNumbers
import Langlands.AlgebraicGeometry.Picard.ArtinianTestDeformations
import Langlands.AlgebraicGeometry.Picard.DualNumberPointedTangent

/-! # Actual Artinian and dual-number pointed Picard fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianDualNumberComparison

open Langlands.AlgebraicGeometry.Deformation
open DualNumberThickening

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual residue-field fibre of the original scheme. -/
abbrev residueSpace := (relativeSpace f).obj (ArtinianTest.residueBase k K)

/-- Its actual structure map to the residue-field spectrum. -/
abbrev residueStructure : residueSpace (K := K) f ⟶ Spec (CommRingCat.of K) :=
  (relativeProjection f).app (ArtinianTest.residueBase k K)

instance residueStructure_isProper [IsProper f] :
    IsProper (residueStructure (K := K) f) :=
  inferInstanceAs (IsProper (pullback.fst (ArtinianTest.residueBase k K).hom f))

/-- The actual relative total space of the dual-number Artinian test. -/
abbrev artinianSpace := (relativeSpace f).obj
  (ArtinianTest.base (ArtinianTest.dualNumbers k K))

private lemma dualBase_structure :
    (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom =
      dualNumberProjection K ≫ (ArtinianTest.residueBase k K).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- Pullback associativity, retaining the two actual projections. -/
def spaceIso : thickening (residueStructure (K := K) f) ≅ artinianSpace (K := K) f where
  hom := pullback.lift (structureMap (residueStructure (K := K) f))
    (projection (residueStructure (K := K) f) ≫
      pullback.snd (ArtinianTest.residueBase k K).hom f) (by
        rw [dualBase_structure, ← Category.assoc]
        change (pullback.snd _ _ ≫ dualNumberProjection K) ≫ _ =
          (pullback.fst _ _ ≫ pullback.snd _ _) ≫ f
        rw [← pullback.condition]
        simpa only [residueStructure, relativeProjection, Category.assoc] using
          congrArg (fun q ↦ projection (residueStructure (K := K) f) ≫ q)
            (pullback.condition (f := (ArtinianTest.residueBase k K).hom) (g := f)))
  inv := pullback.lift
    (pullback.lift
      (pullback.fst (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom f ≫
        dualNumberProjection K)
      (pullback.snd (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom f) (by
        rw [Category.assoc, ← dualBase_structure, pullback.condition]))
    (pullback.fst (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom f) (by
      simp [residueStructure, relativeProjection])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [residueStructure, relativeProjection, Category.assoc, pullback.condition]
    · simp [residueStructure, relativeProjection]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp [residueStructure, relativeProjection, Category.assoc]

@[reassoc (attr := simp)]
lemma spaceIso_hom_fst :
    (spaceIso (K := K) f).hom ≫
      pullback.fst (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom f =
        structureMap (residueStructure (K := K) f) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma spaceIso_hom_snd :
    (spaceIso (K := K) f).hom ≫
      pullback.snd (ArtinianTest.base (ArtinianTest.dualNumbers k K)).hom f =
        projection (residueStructure (K := K) f) ≫
          pullback.snd (ArtinianTest.residueBase k K).hom f :=
  pullback.lift_snd _ _ _

/-- The actual zero section agrees with the original Artinian reduction map. -/
lemma closedPoint_spaceIso :
    closedPoint (residueStructure (K := K) f) ≫ (spaceIso (K := K) f).hom =
      (relativeSpace f).map (ArtinianTest.reduction (ArtinianTest.dualNumbers k K)) := by
  apply pullback.hom_ext
  · simp [residueStructure, relativeProjection, relativeSpace, Over.pullback,
      ArtinianTest.reduction, dualNumberAugmentation]
    rfl
  · simp [relativeSpace, Over.pullback, Category.assoc]

/-- The actual associativity map intertwines both epsilon-scaling maps. -/
lemma scale_spaceIso (c : K) :
    scale (residueStructure (K := K) f) c ≫ (spaceIso (K := K) f).hom =
      (spaceIso (K := K) f).hom ≫ (relativeSpace f).map
        (ArtinianTest.baseMap (ArtinianTest.dualScale k K c)) := by
  apply pullback.hom_ext
  · simp [relativeSpace, Over.pullback, ArtinianTest.baseMap]
    rfl
  · simp [relativeSpace, Over.pullback, Category.assoc]

/-- Ordinary bundle pullback along the actual space isomorphism is an equivalence. -/
def bundleEquivalence :
    PicardGroupoid (artinianSpace (K := K) f) ≌
      PicardGroupoid (thickening (residueStructure (K := K) f)) := by
  let e := spaceIso (K := K) f
  exact CategoryTheory.Equivalence.mk (pullback e.hom) (pullback e.inv)
    ((pullbackComp e.inv e.hom ≪≫
      eqToIso (congrArg pullback e.inv_hom_id) ≪≫
        pullbackId _).symm)
    (pullbackComp e.hom e.inv ≪≫
      eqToIso (congrArg pullback e.hom_inv_id) ≪≫
        pullbackId _)

/-- The ordinary reduction comparison induced by the proved zero-section square. -/
def reductionComparison :
    pullback ((relativeSpace f).map
      (ArtinianTest.reduction (ArtinianTest.dualNumbers k K))) ⋙
        𝟭 (PicardGroupoid (residueSpace (K := K) f)) ≅
      pullback (spaceIso (K := K) f).hom ⋙
        pullback (closedPoint (residueStructure (K := K) f)) :=
  Functor.rightUnitor _ ≪≫
    eqToIso (congrArg pullback (closedPoint_spaceIso (K := K) f).symm) ≪≫
      (pullbackComp (closedPoint (residueStructure (K := K) f))
        (spaceIso (K := K) f).hom).symm

variable (M : LineBundle (residueSpace (K := K) f))

/-- Compare actual pointed objects, retaining the prescribed reduction isomorphism. -/
def pointedFunctor :
    ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K) ⥤
      PointedDeformations (residueStructure (K := K) f) M :=
  StructuredArrow.map₂
    (F := pullback (spaceIso (K := K) f).hom)
    (G := 𝟭 (PicardGroupoid (residueSpace (K := K) f)))
    (𝟙 (Core.mk M)) (reductionComparison (K := K) f).hom

instance pointedFunctor_isEquivalence : (pointedFunctor f M).IsEquivalence := by
  let : (pullback (spaceIso (K := K) f).hom).IsEquivalence :=
    (bundleEquivalence (K := K) f).isEquivalence_functor
  exact StructuredArrow.isEquivalenceMap₂
    (F := pullback (spaceIso (K := K) f).hom)
    (G := 𝟭 (PicardGroupoid (residueSpace (K := K) f)))
    (𝟙 (Core.mk M)) (reductionComparison (K := K) f).hom

/-- The actual Artinian dual-number fibre is the computed pointed dual-number groupoid. -/
def pointedEquivalence :
    ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K) ≌
      PointedDeformations (residueStructure (K := K) f) M :=
  (pointedFunctor f M).asEquivalence

/-- The forward equivalence uses ordinary pullback of the underlying actual bundle. -/
lemma pointedEquivalence_obj_bundle
    (A : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)) :
    ((pointedEquivalence f M).functor.obj A).right.of =
      (LineBundle.pullback (spaceIso (K := K) f).hom).obj A.right.of := rfl

/-- Arrows of the comparison are ordinary pullbacks of actual bundle isomorphisms. -/
lemma pointedEquivalence_map_iso
    {A B : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)}
    (a : A ⟶ B) :
    ((pointedEquivalence f M).functor.map a).right.iso =
      (LineBundle.pullback (spaceIso (K := K) f).hom).mapIso a.right.iso := rfl

private def isoClassesEquiv {C D : Type*} [Category* C] [Category* D] (e : C ≌ D) :
    Quotient (isIsomorphicSetoid C) ≃ Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.map e.functor.obj (fun _ _ ⟨a⟩ ↦ ⟨e.functor.mapIso a⟩)
  invFun := Quotient.map e.inverse.obj (fun _ _ ⟨a⟩ ↦ ⟨e.inverse.mapIso a⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with | h A => ?_
    exact Quotient.sound ⟨(e.unitIso.app A).symm⟩
  right_inv q := by
    induction q using Quotient.inductionOn with | h A => ?_
    exact Quotient.sound ⟨e.counitIso.app A⟩

/-- Isomorphism classes in the actual relative Artinian dual-number fibre. -/
abbrev Classes := Quotient (isIsomorphicSetoid
  (ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)))

/-- The actual pointed-groupoid equivalence descends to its isomorphism classes. -/
def classEquiv : Classes f M ≃
    PointedDeformationClasses (residueStructure (K := K) f) M :=
  isoClassesEquiv (pointedEquivalence f M)

/-- The class comparison is induced by the displayed actual pointed functor. -/
lemma classEquiv_mk
    (A : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)) :
    classEquiv f M (Quotient.mk _ A) =
      Quotient.mk _ ((pointedEquivalence f M).functor.obj A) := rfl

local notation "preservation" =>
  Langlands.Scheme.Modules.pullbackTensorComparisonIsIso

/-- The comparison class retains the ordinary pullback of the actual total-space bundle. -/
lemma classEquiv_ordinary_val
    (A : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)) :
    (pointedClassEquiv (residueStructure (K := K) f) M preservation
      (classEquiv f M (Quotient.mk _ A))).val =
        LineBundle.pullbackHom preservation (spaceIso (K := K) f).hom
          (LineBundle.isoClass preservation A.right.of) := rfl

/-- Actual restriction along epsilon scaling, on actual Artinian pointed classes. -/
def restrictClass (c : K) : Classes f M → Classes f M :=
  Quotient.map
    (ArtinianTestDeformations.restrict f M (ArtinianTest.dualScale k K c)).obj
    (fun _ _ ⟨a⟩ ↦ ⟨(ArtinianTestDeformations.restrict f M
      (ArtinianTest.dualScale k K c)).mapIso a⟩)

/-- The actual Artinian scaling action corresponds to the computed pointed scaling action. -/
lemma classEquiv_restrictClass (c : K) (q : Classes f M) :
    classEquiv f M (restrictClass f M c q) =
      pointedScaleClass (residueStructure (K := K) f) M c (classEquiv f M q) := by
  apply (pointedClassEquiv (residueStructure (K := K) f) M preservation).injective
  apply Subtype.ext
  induction q using Quotient.inductionOn with | h A => ?_
  rw [pointedScaleClass_ordinary_val]
  change LineBundle.pullbackHom preservation (spaceIso (K := K) f).hom
    (LineBundle.pullbackHom preservation
      ((relativeSpace f).map (ArtinianTest.baseMap (ArtinianTest.dualScale k K c)))
      (LineBundle.isoClass preservation A.right.of)) =
    LineBundle.pullbackHom preservation (scale (residueStructure (K := K) f) c)
      (LineBundle.pullbackHom preservation (spaceIso (K := K) f).hom
        (LineBundle.isoClass preservation A.right.of))
  rw [LineBundle.pullbackHom_comp, LineBundle.pullbackHom_comp, scale_spaceIso]

/-- Transfer normalized tensor addition through the actual groupoid comparison. -/
instance classesAddCommGroup : AddCommGroup (Classes f M) := (classEquiv f M).addCommGroup

/-- The class comparison respects the transferred tensor addition. -/
def classAddEquiv : Classes f M ≃+
    PointedDeformationClasses (residueStructure (K := K) f) M :=
  { classEquiv f M with map_add' := fun _ _ ↦ (classEquiv f M).apply_symm_apply _ }

/-- Scalars act by actual Artinian test restriction. -/
instance classesSMul : SMul K (Classes f M) where
  smul := restrictClass f M

lemma classEquiv_smul (c : K) (q : Classes f M) :
    classEquiv f M (c • q) = c • classEquiv f M q :=
  classEquiv_restrictClass f M c q

section SeparatedQuasiCompact

variable [IsSeparated (residueStructure (K := K) f)]
  [QuasiCompact (residueStructure (K := K) f)]

/-- The intrinsic Artinian first-order classes form a module with the actual scalar action. -/
instance classesModule : Module K (Classes f M) :=
  Function.Injective.module K (classAddEquiv f M).toAddMonoidHom
    (classAddEquiv f M).injective (classEquiv_smul f M)

/-- The actual first-order class comparison is linear. -/
def classLinearEquiv : Classes f M ≃ₗ[K]
    PointedDeformationClasses (residueStructure (K := K) f) M :=
  { classAddEquiv f M with map_smul' := classEquiv_smul f M }

/-- Actual relative Artinian first-order classes at every bundle are the residue-fibre H¹. -/
def classH1LinearEquiv (𝒰 : (residueSpace (K := K) f).OrderedAffineCover) :
    Classes f M ≃ₗ[K]
      (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
        (residueStructure (K := K) f) 1).obj
          (Langlands.Scheme.Modules.structureSheaf (residueSpace (K := K) f)) :=
  (classLinearEquiv f M).trans (pointedTangentH1LinearEquiv
    (residueStructure (K := K) f) M 𝒰)

end SeparatedQuasiCompact

/-- Properness of the original family makes these actual residue-field tangents finite. -/
theorem finiteDimensional_classes [IsProper f] : FiniteDimensional K (Classes f M) := by
  let := finiteDimensional_pointedClasses (residueStructure (K := K) f) M
  exact Module.Finite.equiv (classLinearEquiv f M).symm

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianDualNumberComparison
