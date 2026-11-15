import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Extensions of simply connected semisimple groups by groups of multiplicative type split -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, *Algebraic Groups* (2017), Proposition 18.28 in the case singled out by Remark 18.29.
Let `G` be a simply connected semisimple group over a field `k`, and let `q : G' ⟶ G` be an actual
flat, surjective homomorphism from an affine group scheme `G'` of finite type over `k` whose
actual kernel is of multiplicative type. Then `q` has a homomorphic section. -/
def SimplyConnectedMultiplicativeExtensionSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G'.X.hom] [IsAffineHom G'.X.hom] (q : G' ⟶ G),
    IsSimplyConnected G → Flat q.hom.hom.left → Surjective q.hom.hom.left →
    IsMultiplicativeType (kernel q) →
      ∃ s : G ⟶ G', s ≫ q = 𝟙 G

end Langlands.GroupScheme
