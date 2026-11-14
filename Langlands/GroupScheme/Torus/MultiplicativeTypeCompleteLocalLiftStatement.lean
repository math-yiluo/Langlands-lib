import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Statement: lifting homomorphisms from groups of multiplicative type over complete local rings -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Lifting homomorphisms from the special fibre** (Conrad, *Reductive group schemes* (2014),
Corollary B.3.5). Let `S = Spec A` for a complete local noetherian ring `A` with residue field
`k`, let `G` be a smooth affine `S`-group and `H` an `S`-group of multiplicative type. Write
`f₀ = f_k` for the special fibre of a homomorphism `f : H ⟶ G`.
1. Every homomorphism `f₀ : H_k ⟶ G_k` of special fibres lifts to a homomorphism
   `f : H ⟶ G`.
2. Any two lifts `f, f'` of the same homomorphism of special fibres are conjugate under
   `ker(G(S) → G(k))`: there is `g ∈ G(S)` restricting to `1` in `G(k)` with
   `f' = int(g) ∘ f`.
3. If `f_k` is a closed immersion, then so is `f`. -/
def MultiplicativeTypeCompleteLocalLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (G H : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    RelativeMultiplicativeType.IsMultiplicativeType H →
      let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
      (∀ f₀ : (GroupScheme.baseChange sp).obj H ⟶ (GroupScheme.baseChange sp).obj G,
        ∃ f : H ⟶ G, (GroupScheme.baseChange sp).map f = f₀) ∧
      (∀ f f' : H ⟶ G,
        (GroupScheme.baseChange sp).map f = (GroupScheme.baseChange sp).map f' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
          G.constantPoint g (Over.mk sp) = 1 ∧ f' = f ≫ (G.innerIso g).hom) ∧
      (∀ f : H ⟶ G, IsClosedSubgroup ((GroupScheme.baseChange sp).map f) →
        IsClosedSubgroup f)

end Langlands.GroupScheme
