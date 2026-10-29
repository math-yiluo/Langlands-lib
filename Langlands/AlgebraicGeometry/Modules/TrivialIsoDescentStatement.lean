import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Descent of isomorphisms between trivial modules -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule

namespace Langlands.Scheme.Modules

/-- A canonically compatible isomorphism between pullbacks descends uniquely
when both base modules have fixed global trivializations. -/
def TrivialIsoDescentStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ Y), QuasiCompact p → Flat p → Surjective p →
    ∀ (M N : Y.Modules) (_τ : M ≅ structureModule Y) (_σ : N ≅ structureModule Y)
      (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N),
      (∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
        (Scheme.Modules.pullback a).map e.hom ≫ (equalCompositeIso p a b h N).hom =
          (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom) →
      ∃! e₀ : M ≅ N, (Scheme.Modules.pullback p).mapIso e₀ = e

end Langlands.Scheme.Modules
