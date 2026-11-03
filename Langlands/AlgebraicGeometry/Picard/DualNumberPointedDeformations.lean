import Langlands.AlgebraicGeometry.Picard.DualNumberInfinitesimalAutomorphisms
import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationH1
import Langlands.AlgebraicGeometry.Picard.Groupoid
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Pointed lifts in the actual dual-number Picard groupoid -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (M : LineBundle X)

/-- An actual line bundle together with an actual isomorphism from its specified reduction. -/
abbrev PointedDeformations :=
  StructuredArrow (Core.mk M) (PicardGroupoid.pullback (closedPoint f))

/-- Every arrow of pointed deformations is an actual compatible isomorphism. -/
instance pointedDeformationsGroupoid : Groupoid (PointedDeformations f M) :=
  Groupoid.ofIsIso (fun h ↦
    isIso_of_reflects_iso h
      (StructuredArrow.proj (Core.mk M) (PicardGroupoid.pullback (closedPoint f))))

/-- Forgetting the reduction identification identifies actual pointed automorphisms
with the kernel of actual zero-section pullback. -/
def pointedAutKernelEquiv (A : PointedDeformations f M) :
    Aut A ≃* InfinitesimalAut f A.right.of where
  toFun a := ⟨a.hom.right.iso, by
    have h : (PicardGroupoid.pullback (closedPoint f)).map a.hom.right = 𝟙 _ :=
      (cancel_epi A.hom).mp (by simp)
    exact congrArg CoreHom.iso h⟩
  invFun b := StructuredArrow.isoMk (Core.isoMk b.val) (by
    have h : (PicardGroupoid.pullback (closedPoint f)).map
        (Core.isoMk b.val).hom = 𝟙 _ := by
      apply CoreHom.ext
      exact b.property
    rw [h, Category.comp_id])
  left_inv a := by
    apply Iso.ext
    apply StructuredArrow.hom_ext
    apply CoreHom.ext
    rfl
  right_inv b := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl

/-- The kernel comparison keeps the underlying actual bundle automorphism. -/
lemma pointedAutKernelEquiv_val (A : PointedDeformations f M) (a : Aut A) :
    (pointedAutKernelEquiv f M A a).val = a.hom.right.iso :=
  rfl

/-- Every pointed automorphism is uniquely scalar multiplication by `1 + ε a`. -/
def pointedAutGlobalFunctionsEquiv (A : PointedDeformations f M) :
    Aut A ≃* Multiplicative Γ(X, ⊤) :=
  (pointedAutKernelEquiv f M A).trans (infinitesimalAutEquiv f A.right.of).symm

/-- The inverse coefficient comparison is the actual scalar automorphism. -/
lemma pointedAutGlobalFunctionsEquiv_symm_val (A : PointedDeformations f M)
    (a : Γ(X, ⊤)) :
    ((pointedAutGlobalFunctionsEquiv f M A).symm (Multiplicative.ofAdd a)).hom.right.iso =
      LineBundle.unitAutEquiv A.right.of (topUnitsEquiv f (coefficientUnit f ⊤ a)) :=
  rfl

/-- The actual pointed automorphism group, in additive notation, is derived H⁰. -/
def pointedAutH0AddEquiv (A : PointedDeformations f M) :
    Additive (Aut A) ≃+
      (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology f 0).obj
        (SheafOfModules.unit X.ringCatSheaf) :=
  (pointedAutKernelEquiv f M A).toAdditive.trans
    (infinitesimalAutH0LinearEquiv f A.right.of).toAddEquiv

/-- Correct an actual underlying isomorphism to respect the two reduction identifications. -/
lemma pointedDeformations_iso_of_underlying_iso {A B : PointedDeformations f M}
    (e : A.right.of ≅ B.right.of) : Nonempty (A ≅ B) := by
  let F := LineBundle.pullback (closedPoint f)
  let δ : Aut (F.obj B.right.of) :=
    (F.mapIso e).symm ≪≫ A.hom.iso.symm ≪≫ B.hom.iso
  obtain ⟨b, hb⟩ := automorphismReduction_surjective f B.right.of δ
  change F.mapIso b = δ at hb
  refine ⟨StructuredArrow.isoMk (Core.isoMk (e ≪≫ b)) ?_⟩
  apply CoreHom.ext
  change A.hom.iso ≪≫ F.mapIso (e ≪≫ b) = B.hom.iso
  rw [CategoryTheory.Functor.mapIso_trans, hb]
  simp [δ]

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Ordinary actual lift classes of the specified line bundle. -/
def OrdinaryLiftClasses :=
  {q : LineBundle.IsoClasses preservation (thickening f) //
    LineBundle.pullbackHom preservation (closedPoint f) q =
      LineBundle.isoClass preservation M}

/-- Isomorphism classes in the actual pointed-lift groupoid. -/
abbrev PointedDeformationClasses :=
  Quotient (isIsomorphicSetoid (PointedDeformations f M))

/-- Forget the chosen reduction isomorphism on an actual pointed object. -/
def pointedOrdinaryClass (A : PointedDeformations f M) :
    OrdinaryLiftClasses f M preservation :=
  ⟨LineBundle.isoClass preservation A.right.of,
    LineBundle.isoClass_eq_of_iso A.hom.iso.symm⟩

/-- Forget the reduction identification on isomorphism classes. -/
def pointedClassForget :
    PointedDeformationClasses f M → OrdinaryLiftClasses f M preservation :=
  Quotient.lift (pointedOrdinaryClass f M preservation) (fun _ _ ⟨e⟩ ↦
    Subtype.ext (LineBundle.isoClass_eq_of_iso e.hom.right.iso))

/-- Automorphism lifting removes the choice of reduction identification on classes. -/
lemma pointedClassForget_injective :
    Function.Injective (pointedClassForget f M preservation) := by
  intro a b
  induction a using Quotient.inductionOn with | h A => ?_
  induction b using Quotient.inductionOn with | h B => ?_
  intro h
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp (congrArg Subtype.val h)
  exact Quotient.sound (pointedDeformations_iso_of_underlying_iso f M e)

/-- Every ordinary lift admits a chosen reduction identification. -/
lemma pointedClassForget_surjective :
    Function.Surjective (pointedClassForget f M preservation) := by
  intro q
  obtain ⟨L, hL⟩ := Quotient.exists_rep q.val
  change LineBundle.isoClass preservation L = q.val at hL
  have hred :
      LineBundle.isoClass preservation ((LineBundle.pullback (closedPoint f)).obj L) =
        LineBundle.isoClass preservation M := by
    change LineBundle.pullbackHom preservation (closedPoint f)
      (LineBundle.isoClass preservation L) = _
    rw [hL]
    exact q.property
  obtain ⟨α⟩ := LineBundle.isoClass_eq_iff.mp hred
  let A : PointedDeformations f M := StructuredArrow.mk (CoreHom.mk α.symm)
  exact ⟨Quotient.mk _ A, Subtype.ext hL⟩

/-- Pointed lift classes and ordinary actual lift classes agree, for every special-fibre bundle. -/
def pointedClassEquiv :
    PointedDeformationClasses f M ≃ OrdinaryLiftClasses f M preservation :=
  Equiv.ofBijective (pointedClassForget f M preservation)
    ⟨pointedClassForget_injective f M preservation,
      pointedClassForget_surjective f M preservation⟩

/-- At the trivial bundle the actual pointed classes are exactly the computed deformation kernel. -/
def pointedTrivialClassEquiv :
    PointedDeformationClasses f (LineBundle.trivial X) ≃
      DeformationClasses preservation f :=
  pointedClassEquiv f (LineBundle.trivial X) preservation

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
