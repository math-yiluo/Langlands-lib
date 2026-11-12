import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Descent of properties of morphisms of algebraic spaces along cofiltered limits

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file states part (2) of Theorem 3.4 for the properties of
morphisms of algebraic spaces available in the Library: closed immersion, separated, proper,
smooth, affine, open immersion, finite, and fibres nonempty and geometrically connected.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A property `P` of morphisms of algebraic spaces descends along cofiltered limits of affine
schemes, in the sense of Conrad's Theorem 3.4(2): for a morphism `f` of finitely presented
algebraic spaces at a stage, its base change to the limit has `P` if and only if its base
change to some later stage has `P`. -/
def SpaceLimitPropertyDescends
    (P : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop) : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    (i : I) (X Y : AlgebraicSpace (D.obj i)),
    IsQuasiSeparated X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    IsQuasiSeparated Y →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y →
    ∀ f : X ⟶ Y,
      P (baseChangeMap (c.π.app i) f) ↔ ∃ (j : I) (g : j ⟶ i), P (baseChangeMap (D.map g) f)

/-- Conrad's Theorem 3.4(2) for finitely presented algebraic spaces (printed p.13), for the
properties closed immersion, separated, proper, smooth, affine, open immersion, finite, and
fibres nonempty and geometrically connected. -/
def SpaceLimitPropertyDescentStatement : Prop :=
  SpaceLimitPropertyDescends.{u} (fun f => AlgebraicSpace.IsClosedImmersion (hom f)) ∧
    SpaceLimitPropertyDescends.{u} (fun f => IsSeparatedMorphism f) ∧
    SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f) ∧
    SpaceLimitPropertyDescends.{u} (fun f => IsSmoothMorphism f) ∧
    SpaceLimitPropertyDescends.{u} (fun f => IsAffineMorphism (hom f)) ∧
    SpaceLimitPropertyDescends.{u} (fun f => AlgebraicSpace.IsOpenImmersion (hom f)) ∧
    SpaceLimitPropertyDescends.{u} (fun f => AlgebraicSpace.IsFinite (hom f)) ∧
    SpaceLimitPropertyDescends.{u} (fun f => HasGeometricallyConnectedFibres f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
