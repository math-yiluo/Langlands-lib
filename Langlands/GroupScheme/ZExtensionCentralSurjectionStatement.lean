import Langlands.GroupScheme.ZExtension

/-! # Simply connected derived groups under central surjections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected reductive group mapping surjectively with central full kernel to a
connected reductive group with simply connected derived subgroup also has simply
connected derived subgroup. -/
def SimplyConnectedDerivedAscentStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (E G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive E → IsConnectedReductive G →
    ∀ (p : E ⟶ G) [Surjective p.hom.hom.left],
      IsCentral (kernelι p) → HasSimplyConnectedDerivedGroup G →
        HasSimplyConnectedDerivedGroup E

end Langlands.GroupScheme
