import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSmoothStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionProof
import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Smoothness of a chosen dual parameter scheme over a field

Base change to an algebraic closure `Ω` of `k`, identify the pulled-back chosen dual with the
chosen dual of the base-changed abelian scheme by the canonical isomorphism coming from the
universal property on all test schemes, apply the published algebraically closed case, and
descend smoothness along the surjective, flat and quasi-compact morphism `Spec Ω ⟶ Spec k`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The chosen dual parameter scheme of an abelian scheme over an arbitrary field is smooth. -/
theorem fieldDualSchemeSmooth : FieldDualSchemeSmoothStatement.{u} := by
  intro k _ A hA
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let A' : AbelianScheme (Spec (.of Ω)) := (baseChange b).obj A
  have hA' : HasDualScheme A' := hasDualScheme_baseChange picardZeroUniversalBaseChange b A hA
  have : ConnectedSpace A'.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A'.X.hom
  obtain ⟨g, hg⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ A'.X.hom
    inferInstance inferInstance
  have hsmooth' : Smooth (dualScheme A' hA').hom := by
    have := algClosedFieldDualSchemeRelativeDimension Ω A' hA' g hg
    exact SmoothOfRelativeDimension.smooth g _
  let e := dualSchemeBaseChangeIso picardZeroUniversalBaseChange b A hA hA'
  have w : e.hom.left ≫ (dualScheme A' hA').hom = pullback.snd (dualScheme A hA).hom b :=
    Over.w e.hom
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hsnd : Smooth (pullback.snd (dualScheme A hA).hom b) := by
    rw [← w]
    infer_instance
  have hb_surj : Surjective b :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have hb_flat : Flat b :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) _)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := b)
    ⟨⟨hb_surj, hb_flat⟩, inferInstance⟩ hsnd

end Langlands.AbelianScheme
