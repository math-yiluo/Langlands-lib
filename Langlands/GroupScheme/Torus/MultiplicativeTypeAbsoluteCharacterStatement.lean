import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.Representation.Smooth.Definitions
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology

/-! # Absolute-Galois character finiteness and continuity: statements -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual characters of a multiplicative-type group over the chosen
separable closure form a finitely generated integral module. -/
def MultiplicativeTypeAbsoluteCharacterFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType T.toGrp →
      Module.Finite ℤ
        (characterLattice
          ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T))

/-- Every actual character over the chosen separable closure is fixed by an
open subgroup of its Krull automorphism group. No smoothness of the group
scheme is assumed. -/
def MultiplicativeTypeAbsoluteCharacterSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType T.toGrp →
      IsSmooth (characterLattice.galoisRepresentation k (SeparableClosure k) T)

/-- The two membership assertions needed to bundle actual characters as
finitely generated discrete absolute-Galois modules, without a chosen
diagonalizable model or finite splitting field in the hypotheses. -/
def MultiplicativeTypeAbsoluteCharacterStatement : Prop :=
  MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u} ∧
    MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}

end Langlands.GroupScheme
