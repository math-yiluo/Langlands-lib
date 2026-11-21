import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Absolute.TriangularCharacterKernelDescent
import Langlands.GroupScheme.Reductive.RelativeRootCommutatorMap
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Semisimple

/-! # Semisimple conjugation on a connected commutative unipotent normal subgroup -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne, Lemma 16.39. In a smooth connected affine group `G` over an algebraically
closed field, let `N` be a smooth connected commutative unipotent normal closed subgroup
and let `s : G(k)` be semisimple. For a representative `c : C ⟶ N` of `C_N(s)`, the
scheme `C` is connected and the morphism `N × C ⟶ N`, `(x, y) ↦ [s, x] c(y)`,
is surjective. -/
def SemisimpleUnipotentCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G N : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth N.X.hom] [ConnectedSpace N.X.left] [IsCommMonObj N.X]
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : (SubgroupFunctor.range n).IsNormal),
    IsUnipotent N →
    ∀ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (∀ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
        Module.End.IsSemisimple
          (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin m) (Fin m) k))) →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ N),
      ((G.pointCentralizer s).comap n).IsRepresentedBy c →
      letI : Mono n.hom.hom := hn.mono_overHom
      let d := (LinearKernelTower.normalConjugation n hN).commutatorMap s
      ConnectedSpace C.X.left ∧
        Surjective (((fst N.X C.X ≫ d) * (snd N.X C.X ≫ c.hom.hom)).left)

end Langlands.GroupScheme
