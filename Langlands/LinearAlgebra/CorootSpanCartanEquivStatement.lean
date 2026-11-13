import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-! # Based root data with spanning coroots are determined by their Cartan matrix: statement -/

universe u

namespace Langlands.LinearAlgebra

/-- Two finite reduced root data `P` and `Q` over `ℤ` whose coroots span the whole
coweight lattice, with bases `b` and `c`, are isomorphic as soon as some bijection `e`
of their simple roots preserves all simple pairings; moreover the isomorphism of root
data can be chosen to extend `e` on the simple roots. -/
def CorootSpanCartanEquivStatement : Prop :=
  ∀ (ι M N ι' M' N' : Type u) [Finite ι] [Finite ι']
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    (P : RootDatum ι M N) (Q : RootDatum ι' M' N') [P.IsReduced] [Q.IsReduced]
    (b : P.Base) (c : Q.Base),
    P.corootSpan ℤ = ⊤ → Q.corootSpan ℤ = ⊤ →
    ∀ e : b.support ≃ c.support,
      (∀ i j : b.support, Q.pairing (e i) (e j) = P.pairing i j) →
        ∃ f : RootPairing.Equiv P Q, ∀ i : b.support, f.indexEquiv i = e i

end Langlands.LinearAlgebra
