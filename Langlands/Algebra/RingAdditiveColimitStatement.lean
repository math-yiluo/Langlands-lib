import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Colimit.Module

/-! # Underlying additive colimits of directed systems of commutative rings -/

universe uI uA uR

namespace Langlands.Algebra

/-- A bijective ring direct-limit comparison induces a bijective additive comparison for
the same directed system and cocone. -/
def RingAdditiveColimitStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A : ι → Type uA) [∀ i, CommRing (A i)]
    (R : Type uR) [CommRing R]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (g : ∀ i, A i →+* R)
    (hg : ∀ i j h a, g j (f i j h a) = g i a),
    letI := Classical.decEq ι
    Function.Bijective (Ring.DirectLimit.lift A (fun i j h ↦ f i j h) R g hg) →
      Function.Bijective
        (AddCommGroup.DirectLimit.lift A (fun i j h ↦ (f i j h).toAddMonoidHom)
          R (fun i ↦ (g i).toAddMonoidHom) hg)

end Langlands.Algebra
