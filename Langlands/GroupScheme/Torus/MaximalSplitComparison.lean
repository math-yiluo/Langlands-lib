import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Comparing maximal tori with maximal split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every group scheme over `k` which becomes a split torus after a field extension
is already a split torus over `k`. This definition does not assert the property holds. -/
def ToriAreSplit (k : Type u) [Field k] : Prop :=
  ∀ (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T → IsSplitTorus T

variable {k : Type u} [Field k]

/-- Under the explicit splitting property, the two torus predicates agree. -/
theorem ToriAreSplit.isTorus_iff (hsplit : ToriAreSplit k)
    (T : GroupScheme (Spec (CommRingCat.of k))) : IsTorus T ↔ IsSplitTorus T :=
  ⟨hsplit T, IsSplitTorus.isTorus⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- A maximal torus whose torus is split is a maximal split torus. -/
theorem IsMaximalTorus.isMaximalSplitTorus {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    (hT : IsSplitTorus T.toGrp) : IsMaximalSplitTorus i :=
  ⟨⟨hT, hi.2.1⟩, fun T' i' hi' f hf => hi.2.2 T' i' f hi'.1.isTorus hi'.2 hf⟩

/-- If every torus over the base field is split, a maximal split torus is a maximal torus. -/
theorem IsMaximalSplitTorus.isMaximalTorus (hi : IsMaximalSplitTorus i)
    (hsplit : ToriAreSplit k) : IsMaximalTorus i := by
  refine ⟨hi.1.1.isTorus, hi.1.2, ?_⟩
  intro T' i' f hT' hi' hf
  exact hi.2 T' i' ⟨hsplit T'.toGrp hT', hi'⟩ f hf

/-- Under the explicit splitting property, maximal tori and maximal split tori agree. -/
theorem ToriAreSplit.isMaximalTorus_iff (hsplit : ToriAreSplit k)
    (i : T.toGrp ⟶ G) : IsMaximalTorus i ↔ IsMaximalSplitTorus i :=
  ⟨fun hi => hi.isMaximalSplitTorus (hsplit T.toGrp hi.1),
    fun hi => hi.isMaximalTorus hsplit⟩

end Langlands.GroupScheme
