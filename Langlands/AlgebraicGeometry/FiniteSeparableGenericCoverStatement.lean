import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.Separable

/-! # A finite étale cover with prescribed generic residue field -/

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The generic-extension construction in the proof of Stacks 0551, recorded
with an actual residue-field spectrum isomorphism and its structural triangle. -/
def FiniteSeparableGenericCover : Prop :=
  ∀ {Y : Scheme.{u}} [IrreducibleSpace Y] (η : Y),
    IsGenericPoint η univ →
    ∀ (L : Type u) [Field L] [Algebra (Y.residueField η) L]
      [FiniteDimensional (Y.residueField η) L]
      [Algebra.IsSeparable (Y.residueField η) L],
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∃ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsAffine Y' ∧ IrreducibleSpace Y' ∧
        Surjective g ∧ IsFinite g ∧ Etale g ∧
        ∃ η' : Y', IsGenericPoint η' univ ∧
          ∃ e : Spec (.of L) ≅ Spec (Y'.residueField η'),
            e.hom ≫ Y'.fromSpecResidueField η' ≫ g ≫ V.ι =
              Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField η) L)) ≫
                Y.fromSpecResidueField η

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
