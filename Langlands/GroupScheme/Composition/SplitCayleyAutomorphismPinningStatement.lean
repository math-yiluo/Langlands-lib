import Langlands.GroupScheme.Composition.CayleyAutomorphismGroup
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Rational.Characters
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The automorphism group of the split Cayley datum is split adjoint of type `G₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `K`, the actual automorphism group scheme of the split Cayley datum
(Zorn vector matrices) has trivial scheme-theoretic centre and carries a split pinning whose
coroots span the full cocharacter lattice and whose simple roots, under some numbering by
`Fin 2`, have Cartan matrix `CartanMatrix.G₂`. It is proved as
`splitCayleyAutomorphismPinning` in
`Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Pinning`. -/
def SplitCayleyAutomorphismPinningStatement : Prop :=
  ∀ (K : Type u) [Field K],
    center (CayleyDatum.split K).automorphismGroup = ⊥ ∧
      ∃ p : SplitPinning (CayleyDatum.split K).automorphismGroup,
        p.rootDatum.corootSpan ℤ = ⊤ ∧
          ∃ e : p.base.support ≃ Fin 2,
            ∀ a b : p.base.support, p.rootDatum.pairing a b = CartanMatrix.G₂ (e a) (e b)

end Langlands.GroupScheme
