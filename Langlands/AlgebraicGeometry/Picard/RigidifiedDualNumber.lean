import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation

/-! # Rigidified classes restricting to the trivial class -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Rigidified classes whose restriction along `i` is the canonical trivial class.
The data remember a class, not a chosen trivialization of its restriction. -/
def TrivialRestrictionClasses {T : Over S} (i : Over.mk (𝟙 S) ⟶ T) :=
  {q : Classes f ε section_eq T //
    classesPullback f ε section_eq i q =
      classOf f ε section_eq (relativeTrivial f ε section_eq (Over.mk (𝟙 S)))}

variable {P : Over S} (L : relative f ε section_eq P)
  (hL : IsUniversal f ε section_eq L)

/-- Universal classification restricts to the fibres over the trivial class. -/
def classifyingTrivialRestrictionEquiv {T : Over S} (i : Over.mk (𝟙 S) ⟶ T) :
    {t : T ⟶ P // i ≫ t = trivialParameter f ε section_eq L hL} ≃
      TrivialRestrictionClasses f ε section_eq i :=
  (classifyingEquiv f ε section_eq L hL T).subtypeEquiv fun t ↦ by
    change (i ≫ t = trivialParameter f ε section_eq L hL) ↔
      classesPullback f ε section_eq i (classifyingMap f ε section_eq L T t) =
        classOf f ε section_eq (relativeTrivial f ε section_eq (Over.mk (𝟙 S)))
    rw [← classifyingMap_comp f ε section_eq RigidifiedModule.pullbackCoherence]
    have he :
        classifyingMap f ε section_eq L (Over.mk (𝟙 S))
            (trivialParameter f ε section_eq L hL) =
          classOf f ε section_eq (relativeTrivial f ε section_eq (Over.mk (𝟙 S))) :=
      classifyFamily_spec f ε section_eq L hL _
    rw [← he]
    exact ⟨congrArg (classifyingMap f ε section_eq L (Over.mk (𝟙 S))),
      fun h ↦ (hL (Over.mk (𝟙 S))).injective h⟩

@[simp]
lemma classifyingTrivialRestrictionEquiv_val {T : Over S}
    (i : Over.mk (𝟙 S) ⟶ T)
    (t : {t : T ⟶ P // i ≫ t = trivialParameter f ε section_eq L hL}) :
    (classifyingTrivialRestrictionEquiv f ε section_eq L hL i t).val =
      classifyingMap f ε section_eq L T t.val :=
  rfl

end RigidifiedLineBundle

variable (k : Type u) [Field k]

/-- The dual-number test scheme with its specified structure morphism. -/
def dualNumberTest : Over (Spec (CommRingCat.of k)) :=
  Over.mk (dualNumberProjection k)

/-- The augmentation as a morphism of schemes over the field. -/
def dualNumberClosedPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ dualNumberTest k :=
  Over.homMk (dualNumberAugmentation k)
    dualNumberAugmentation_comp_dualNumberProjection

variable {k}

/-- Forgetting slice data identifies the restriction fibre with actual
dual-number scheme maps satisfying the two tangent equations. -/
def dualNumberTangentEquiv (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) :
    {t : dualNumberTest k ⟶ P // dualNumberClosedPoint k ≫ t = e} ≃
      {t : Spec (CommRingCat.of (DualNumber k)) ⟶ P.left //
        IsTangentVectorAt P.hom e.left t} where
  toFun t := ⟨t.val.left, Over.w t.val, congrArg (fun a ↦ a.left) t.property⟩
  invFun t := ⟨Over.homMk t.val t.property.1,
    Over.OverMorphism.ext t.property.2⟩
  left_inv _t := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv _t := Subtype.ext rfl

@[simp]
lemma dualNumberTangentEquiv_val (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P)
    (t : {t : dualNumberTest k ⟶ P // dualNumberClosedPoint k ≫ t = e}) :
    (dualNumberTangentEquiv P e t).val = t.val.left :=
  rfl

namespace RigidifiedLineBundle

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (ε : Spec (CommRingCat.of k) ⟶ X) (section_eq : ε ≫ f = 𝟙 _)

/-- First-order rigidified classes: classes on the dual-number test whose
augmentation pullback is the canonical trivial rigidified class. -/
abbrev FirstOrderClasses :=
  TrivialRestrictionClasses f ε section_eq (dualNumberClosedPoint k)

variable {P : Over (Spec (CommRingCat.of k))}
  (L : relative f ε section_eq P) (hL : IsUniversal f ε section_eq L)

/-- Actual dual-number tangent maps at the trivial parameter are in bijection
with first-order rigidified classes. This is an equivalence of types. -/
def firstOrderClassifyingEquiv :
    {t : Spec (CommRingCat.of (DualNumber k)) ⟶ P.left //
      IsTangentVectorAt P.hom (trivialParameter f ε section_eq L hL).left t} ≃
      FirstOrderClasses f ε section_eq :=
  (dualNumberTangentEquiv P (trivialParameter f ε section_eq L hL)).symm.trans
    (classifyingTrivialRestrictionEquiv f ε section_eq L hL (dualNumberClosedPoint k))

@[simp]
lemma firstOrderClassifyingEquiv_val
    (t : {t : Spec (CommRingCat.of (DualNumber k)) ⟶ P.left //
      IsTangentVectorAt P.hom (trivialParameter f ε section_eq L hL).left t}) :
    (firstOrderClassifyingEquiv f ε section_eq L hL t).val =
      classifyingMap f ε section_eq L (dualNumberTest k)
        (Over.homMk t.val t.property.1) :=
  rfl

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
