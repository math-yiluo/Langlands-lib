import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.Reductive.SpecialLinear
import Langlands.GroupScheme.CentralSimpleNormOne

/-! # Inner forms of the special linear group are reduced-norm-one groups: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `K` be a field and `G` a group scheme over `K`. Suppose `G` is presented as an
inner form of a quasi-split group whose model is isomorphic to the special linear group
scheme `SL_{n+1}` over `K`. Then `G` is isomorphic to the reduced-norm-one group of a
central simple `K`-algebra of reduced degree `n + 1`. -/
def SpecialLinearInnerFormNormOneStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ)
    (e : QuasiSplitInnerForm G),
    Nonempty (e.model ≅ SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) →
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A)
        (_ : FiniteDimensional K A) (_ : Algebra.IsCentral K A) (_ : IsSimpleRing A),
        Langlands.CentralSimple.reducedDegree K A = n + 1 ∧
          Nonempty (G ≅ CentralSimpleUnits.normOne K A)

end Langlands.GroupScheme
