import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStatements
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedGeneral
import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective

/-! # Conditional faithfully flat separation of rigidified classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Scheme.Modules

/-- Compatibility with canonical descent comparisons is inherited under precomposition. -/
lemma equalComposite_compatible_precomp {X Y U V : Scheme.{u}} (p : X ⟶ Y)
    (a b : U ⟶ X) (hab : a ≫ p = b ≫ p) {M N : Y.Modules}
    (e : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (he : (Scheme.Modules.pullback a).map e ≫ (equalCompositeIso p a b hab N).hom =
      (equalCompositeIso p a b hab M).hom ≫ (Scheme.Modules.pullback b).map e)
    (k : V ⟶ U) (h : (k ≫ a) ≫ p = (k ≫ b) ≫ p) :
    (Scheme.Modules.pullback (k ≫ a)).map e ≫
        (equalCompositeIso p (k ≫ a) (k ≫ b) h N).hom =
      (equalCompositeIso p (k ≫ a) (k ≫ b) h M).hom ≫
        (Scheme.Modules.pullback (k ≫ b)).map e := by
  have na := (Scheme.Modules.pullbackComp k a).hom.naturality e
  have nb := (Scheme.Modules.pullbackComp k b).hom.naturality e
  simp only [Functor.comp_map] at na nb
  apply (cancel_epi ((Scheme.Modules.pullbackComp k a).hom.app
    ((Scheme.Modules.pullback p).obj M))).mp
  simp only [← Category.assoc]
  rw [← na]
  simp only [Category.assoc]
  rw [equalCompositeIso_precomp_hom p a b N k hab h,
    equalCompositeIso_precomp_hom_assoc p a b M k hab h, ← nb]
  rw [← Functor.map_comp_assoc, he, Functor.map_comp]
  simp only [Category.assoc]

/-- It suffices to check compatibility on the two projections of the actual overlap. -/
lemma equalComposite_compatible_of_pullback {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M N : Y.Modules}
    (e : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (he : (Scheme.Modules.pullback (pullback.fst p p)).map e ≫
        (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition N).hom =
      (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition M).hom ≫
        (Scheme.Modules.pullback (pullback.snd p p)).map e)
    (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map e ≫ (equalCompositeIso p a b h N).hom =
      (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e := by
  have hx := equalComposite_compatible_precomp p (pullback.fst p p) (pullback.snd p p)
    pullback.condition e he (pullback.lift a b h)
    (by simp only [pullback.lift_fst, pullback.lift_snd, h])
  have ha : pullback.lift a b h ≫ pullback.fst p p = a := pullback.lift_fst _ _ _
  have hb : pullback.lift a b h ≫ pullback.snd p p = b := pullback.lift_snd _ _ _
  let P (c d : U ⟶ X) : Prop := ∀ (hcd : c ≫ p = d ≫ p),
    (Scheme.Modules.pullback c).map e ≫ (equalCompositeIso p c d hcd N).hom =
      (equalCompositeIso p c d hcd M).hom ≫ (Scheme.Modules.pullback d).map e
  have hx' : P (pullback.lift a b h ≫ pullback.fst p p)
      (pullback.lift a b h ≫ pullback.snd p p) := fun _ => hx
  exact ((congrArg₂ P ha hb).mp hx') h

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.Scheme.Modules
open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- An actual relative rigidified isomorphism satisfies the full module descent condition. -/
lemma relative_iso_descent_compatible
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) (L M : relative f ε section_eq T)
    (e : (relativePullback f ε section_eq h).obj L ≅
      (relativePullback f ε section_eq h).obj M)
    (V : Scheme.{u}) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    (Scheme.Modules.pullback a).map e.hom.hom.val ≫
        (equalCompositeIso ((relativeSpace f).map h) a b hab M.obj.carrier).hom =
      (equalCompositeIso ((relativeSpace f).map h) a b hab L.obj.carrier).hom ≫
        (Scheme.Modules.pullback b).map e.hom.hom.val := by
  apply equalComposite_compatible_of_pullback
  exact rigidified_overlap_compatible f ε section_eq unique h h L M e e

/-- The ordinary carrier isomorphism obtained by faithfully flat descent of a rigidified one. -/
def descendedCarrierIso
    (hD1 : LineBundleIsoDescentStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) [QuasiCompact h.left] [Flat h.left] [Surjective h.left]
    (L M : relative f ε section_eq T)
    (e : (relativePullback f ε section_eq h).obj L ≅
      (relativePullback f ε section_eq h).obj M) :
    L.obj.carrier ≅ M.obj.carrier :=
  Classical.choose (hD1 _ _ ((relativeSpace f).map h)
    (relativeSpace_map_quasiCompact f h) (relativeSpace_map_flat f h)
    (relativeSpace_map_surjective f h) L.obj.carrier M.obj.carrier L.property M.property
    ((forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso e)
    (relative_iso_descent_compatible f ε section_eq unique h L M e))

/-- Under line-bundle isomorphism descent, rigidified classes are separated for every
quasi-compact faithfully flat slice morphism. -/
lemma classes_flatSeparated_of_isoDescent
    (hD1 : LineBundleIsoDescentStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) [QuasiCompact h.left] [Flat h.left] [Surjective h.left]
    (q r : Classes f ε section_eq T)
    (he : classesPullback f ε section_eq h q = classesPullback f ε section_eq h r) :
    q = r := by
  apply forgetClasses_injective f ε section_eq T
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      obtain ⟨e⟩ := Quotient.exact he
      apply (RelativePicard.classOf_eq_iff_iso f T _ _).2
      exact ⟨ObjectProperty.isoMk _ (descendedCarrierIso f ε section_eq hD1 unique h L M e)⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
