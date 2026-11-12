import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Eventual equality of morphisms and uniqueness of models of algebraic spaces

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file states, along a cofiltered limit of affine schemes, the
injectivity half of Theorem 3.4(1) (two morphisms at a stage that agree over the limit agree at
a later stage) and Theorem 3.4(3) (essential uniqueness of models up to essentially unique
isomorphism).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open BaseChangeComparison

/-- Eventual equality of morphisms of finitely presented algebraic spaces along a cofiltered
limit of affine schemes. Two morphisms at a stage whose base changes to the limit are equal
have equal base changes to some later stage. -/
def SpaceLimitMorphismEventualEquality : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    (i : I) (X Y : AlgebraicSpace (D.obj i)),
    IsQuasiSeparated X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    IsQuasiSeparated Y →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y →
    ∀ φ ψ : X ⟶ Y, baseChangeMap (c.π.app i) φ = baseChangeMap (c.π.app i) ψ →
      ∃ (j : I) (f : j ⟶ i), baseChangeMap (D.map f) φ = baseChangeMap (D.map f) ψ

/-- Essential uniqueness of models of finitely presented algebraic spaces along a cofiltered
limit of affine schemes. Two models at a stage with an isomorphism `e` of their base changes to
the limit become isomorphic at a later stage by an isomorphism whose base change to the limit
is `e`, through the iterated base-change comparison `compIso`; two such isomorphisms at one
stage become equal at a later stage. -/
def SpaceLimitModelUniqueness : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    (i : I) (X X' : AlgebraicSpace (D.obj i)),
    IsQuasiSeparated X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    IsQuasiSeparated X' →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X' →
    ∀ e : baseChange (c.π.app i) X ≅ baseChange (c.π.app i) X',
      (∃ (j : I) (f : j ⟶ i) (h : baseChange (D.map f) X ≅ baseChange (D.map f) X'),
        baseChangeMap (c.π.app j) h.hom =
          (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X).hom ≫ e.hom ≫
            (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X').inv) ∧
      ∀ (j : I) (f : j ⟶ i) (h h' : baseChange (D.map f) X ≅ baseChange (D.map f) X'),
        baseChangeMap (c.π.app j) h.hom =
            (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X).hom ≫ e.hom ≫
              (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X').inv →
        baseChangeMap (c.π.app j) h'.hom =
            (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X).hom ≫ e.hom ≫
              (compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X').inv →
        ∃ (k : I) (f' : k ⟶ j),
          baseChangeMap (D.map f') h.hom = baseChangeMap (D.map f') h'.hom

/-- Conrad's Theorem 3.4 for finitely presented algebraic spaces (printed p.13): eventual
equality of morphisms (the injectivity half of part (1)) and uniqueness of models (part (3)). -/
def SpaceLimitUniquenessStatement : Prop :=
  SpaceLimitMorphismEventualEquality.{u} ∧ SpaceLimitModelUniqueness.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace
