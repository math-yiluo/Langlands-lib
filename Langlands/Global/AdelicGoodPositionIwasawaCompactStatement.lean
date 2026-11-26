import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Maximal compact subgroups in good position with Iwasawa coverage

For a parabolic subgroup `P` of a connected reductive group over a number field there are a
standard parabolic family and a maximal compact subgroup `K` of `G(𝔸)` in good position with
respect to it (Mœglin–Waldspurger I.1.4; Bernstein–Lapid §2.1) such that `P(𝔸)K = G(𝔸)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- A maximal compact subgroup in good position with Iwasawa coverage for a given parabolic.
Let `G` be a connected reductive group over a number field `F` and `p : P → G` a parabolic
subgroup. There are a standard parabolic family `𝓕` of `G` and a maximal compact subgroup `K`
of `G(𝔸)` such that `P(𝔸)K = G(𝔸)`, `P₀(𝔸)K = G(𝔸)` for the minimal standard parabolic `P₀`
of `𝓕`, and `K ∩ M_J(𝔸)` is a maximal compact subgroup of `M_J(𝔸)` for every standard Levi
subgroup `M_J` of `𝓕`. -/
def GoodPositionIwasawaCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left],
    IsConnectedReductive G → IsParabolicSubgroup p →
    ∃ (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
      IsMaximalCompactSubgroup F G K ∧ IsIwasawaCompact p K ∧
      IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K ∧
      ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
        (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)

end Langlands.Global
