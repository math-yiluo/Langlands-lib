import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.Separable

/-! # Finite separable splitting of actual irreducible components -/

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks 054R: a locally finite-type scheme over a field with finitely many
actual components has a finite separable scalar extension over which all
actual maximal components are geometrically irreducible. -/
def FiniteSeparableComponentSplitting : Prop :=
  ∀ (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [Finite (irreducibleComponents X)],
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
      ∀ C : irreducibleComponents
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
        GeometricallyIrreducible
          ((Scheme.IdealSheafData.vanishingIdeal
            (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
              TopologicalSpace.Closeds
                (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}))).subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))))

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
