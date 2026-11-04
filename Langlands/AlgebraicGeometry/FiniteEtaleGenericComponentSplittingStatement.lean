import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite étale splitting of actual generic-fibre components -/

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every actual maximal irreducible fibre component, equipped with its
vanishing-ideal closed subscheme structure, is geometrically irreducible. -/
def FiberComponentsGeometricallyIrreducible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) : Prop :=
  ∀ C : irreducibleComponents (f.fiber y),
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
          TopologicalSpace.Closeds (f.fiber y))).subschemeι ≫
        f.fiberToSpecResidueField y)

/-- Stacks Lemma 37.24.8 (0551), using an actual pullback of the open
restriction and the actual reduced closed subschemes of its fibre components. -/
def FiniteTypeFiniteEtaleGenericComponentSplitting : Prop :=
  ∀ {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f],
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∃ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsAffine Y' ∧ IrreducibleSpace Y' ∧
        Surjective g ∧ IsFinite g ∧ Etale g ∧
        Surjective (pullback.fst (f ∣_ V) g) ∧
        IsFinite (pullback.fst (f ∣_ V) g) ∧
        Etale (pullback.fst (f ∣_ V) g) ∧
        ∃ η' : Y', IsGenericPoint η' univ ∧
          FiberComponentsGeometricallyIrreducible (pullback.snd (f ∣_ V) g) η'

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
