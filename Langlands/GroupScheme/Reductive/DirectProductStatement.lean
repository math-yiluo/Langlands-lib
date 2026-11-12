import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Products

/-! # Direct products of pseudo-reductive, reductive and semisimple groups: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

/-- **Direct products** (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd edition
(2015); Conrad, *Reductive group schemes*). For group schemes `G` and `H` over a field `k`,
the direct product `G ⊗ H` is pseudo-reductive, connected reductive, or semisimple whenever
both factors are. -/
def DirectProductReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
    (IsPseudoReductive G → IsPseudoReductive H → IsPseudoReductive (G ⊗ H)) ∧
    (IsConnectedReductive G → IsConnectedReductive H → IsConnectedReductive (G ⊗ H)) ∧
    (IsSemisimple G → IsSemisimple H → IsSemisimple (G ⊗ H))

end Langlands.GroupScheme
