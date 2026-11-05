import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Torus.Split

/-! # Statement: injective character and cocharacter maps give an isogeny of split tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isogenies of split tori from lattice maps** (derived from Milne Theorem 12.9 and the
remark after Definition 23.1). A homomorphism `t : T ⟶ T'` of split tori over a field whose
character map `χ ↦ t ≫ χ` and cocharacter map `ν ↦ ν ≫ t` are both injective is an isogeny:
its underlying morphism of schemes is finite, flat and surjective. -/
def SplitTorusIsogenyOfLatticeMapsStatement : Prop :=
  ∀ (k : Type u) [Field k] (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ T'),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    Function.Injective (fun χ : characterLattice T' => t ≫ χ) →
    Function.Injective (fun ν : cocharacterLattice T => ν ≫ t) →
      IsIsogeny (CommGroupScheme.groupHom t)

end Langlands.GroupScheme
