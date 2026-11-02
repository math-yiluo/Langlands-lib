import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Faithfully flat descent of line bundles: statements

Two internal interface propositions used for the fppf sheaf property of rigidified Picard
classes: descent of isomorphisms between line bundles along quasi-compact flat surjections
(`LineBundleIsoDescentStatement`) and effectivity of descent data for line bundles along affine
flat surjections (`LineBundleDescentEffectiveStatement`). Both are special cases of fpqc descent
of quasi-coherent sheaves (Stacks Project, Tag 023T) combined with descent of finite local
freeness (Stacks Project, Tag 05B2). Descent data are written in the equal-composite form: for
every scheme `U` and every pair `a b : U ⟶ X` with `a ≫ p = b ≫ p`. -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

namespace Langlands.Scheme.Modules

/-- Isomorphisms between line bundles descend uniquely along quasi-compact faithfully flat
morphisms, when they are compatible with the canonical comparisons on all pairs of maps with
equal composites. -/
def LineBundleIsoDescentStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ Y), QuasiCompact p → Flat p → Surjective p →
    ∀ (M N : Y.Modules), IsLocallyFreeRankOne M → IsLocallyFreeRankOne N →
    ∀ (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N),
      (∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
        (Scheme.Modules.pullback a).map e.hom ≫ (equalCompositeIso p a b h N).hom =
          (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom) →
      ∃! e₀ : M ≅ N, (Scheme.Modules.pullback p).mapIso e₀ = e

/-- A line bundle on the source of an affine faithfully flat morphism, with descent
isomorphisms on all pairs of maps with equal composites that are natural under
precomposition and satisfy the cocycle law, is the pullback of a line bundle on the target. -/
def LineBundleDescentEffectiveStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ Y), IsAffineHom p → Flat p → Surjective p →
    ∀ (F : X.Modules), IsLocallyFreeRankOne F →
    ∀ (θ : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p →
        ((Scheme.Modules.pullback a).obj F ≅ (Scheme.Modules.pullback b).obj F)),
      (∀ (U V : Scheme.{u}) (k : V ⟶ U) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
          (h' : (k ≫ a) ≫ p = (k ≫ b) ≫ p),
        (θ V (k ≫ a) (k ≫ b) h').hom =
          (Scheme.Modules.pullbackComp k a).inv.app F ≫
            (Scheme.Modules.pullback k).map (θ U a b h).hom ≫
              (Scheme.Modules.pullbackComp k b).hom.app F) →
      (∀ (U : Scheme.{u}) (a b c : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p)
          (h'' : a ≫ p = c ≫ p),
        (θ U a b h).hom ≫ (θ U b c h').hom = (θ U a c h'').hom) →
      ∃ M : Y.Modules, IsLocallyFreeRankOne M ∧
        Nonempty ((Scheme.Modules.pullback p).obj M ≅ F)

end Langlands.Scheme.Modules
