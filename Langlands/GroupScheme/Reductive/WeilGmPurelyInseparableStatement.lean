import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.WeilRestriction
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # A pseudo-reductive group that is not reductive: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **`R_{k'/k}(GL_1)` for a purely inseparable `k'/k` is pseudo-reductive but not reductive**
(Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2015), Example 1.1.3). Let `k'/k` be a
finite purely inseparable field extension of degree `> 1`, so that `k` is imperfect. Then the
Weil restriction `R_{k'/k}(𝔾_m)`, the group scheme over `k` with points `(k' ⊗_k A)ˣ`, is
pseudo-reductive over `k` and is not connected reductive. -/
def WeilGmPurelyInseparablePseudoReductiveStatement : Prop :=
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsPurelyInseparable k k'], 1 < Module.finrank k k' →
    IsPseudoReductive (WeilGm.groupScheme (CommRingCat.of k) k') ∧
      ¬ IsConnectedReductive (WeilGm.groupScheme (CommRingCat.of k) k')

end Langlands.GroupScheme
