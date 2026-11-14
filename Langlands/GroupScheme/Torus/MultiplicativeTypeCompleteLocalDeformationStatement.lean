import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Statement: deforming groups of multiplicative type over complete local rings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Homomorphisms into deformations of groups of multiplicative type** (Conrad, *Reductive
group schemes* (2014), Theorem B.3.2(2); compare SGA 3, IX, 7.1). Let `S = Spec A` for a complete
local noetherian ring `A` with residue field `k`, let `G` be a flat affine `S`-group of finite
type whose special fibre `G_k` is of multiplicative type, and let `H` be an `S`-group that
becomes diagonalizable over a finite étale cover of `S`. Then
1. every homomorphism `f₀ : H_k ⟶ G_k` of special fibres is the special fibre of exactly one
   homomorphism `f : H ⟶ G`;
2. if the special fibre of `f : H ⟶ G` is an isomorphism, then `f` is an open and closed
   immersion. -/
def MultiplicativeTypeCompleteLocalDeformationStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (G H : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [Flat G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
      IsMultiplicativeType ((GroupScheme.baseChange sp).obj G) →
        (∀ f₀ : (GroupScheme.baseChange sp).obj H ⟶ (GroupScheme.baseChange sp).obj G,
          ∃! f : H ⟶ G, (GroupScheme.baseChange sp).map f = f₀) ∧
        (∀ f : H ⟶ G, IsIso ((GroupScheme.baseChange sp).map f) →
          IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left)

end Langlands.GroupScheme
