import Langlands.GroupScheme.Reductive.SpecialLinear
import Langlands.GroupScheme.Reductive.Pinning
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # A simply connected pinning of type `A_n` of the special linear group: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k` and for every `n`, the actual special linear group scheme
`SL_{n+1}` over `k` has a split pinning whose coroots span the whole cocharacter lattice
over `ℤ` (the simply connected condition), and whose simple roots can be numbered by
`Fin n` so that their pairings form the Cartan matrix of type `A_n`. -/
def SpecialLinearSimplyConnectedPinningStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    haveI := SpecialLinear.isAffineHom_groupScheme (Fin (n + 1)) (CommRingCat.of k)
    ∃ p : SplitPinning (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)),
      p.rootDatum.corootSpan ℤ = ⊤ ∧
        ∃ e : p.base.support ≃ Fin n,
          ∀ a b : p.base.support, p.rootDatum.pairing a b = CartanMatrix.A n (e a) (e b)

end Langlands.GroupScheme
