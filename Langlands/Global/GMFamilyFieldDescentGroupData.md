# Linear-algebra descent data from a split torus with an integral root datum

This module produces the abstract descent data `FieldDescentData`
([GMFamilyFieldDescentMetric](../LinearAlgebra/GMFamilyFieldDescentMetric.md)) from group data over a field `K`.
Declarations are in `Langlands.GMFamily.FieldDescentTori`.

- `rootFunctionals hT t` is the finite set of real functionals `eval T γ` of the relative roots of
  a split torus `t : T ⟶ G`, and `rootMult hT t ℓ` the total dimension of the weight spaces of the
  roots with functional `ℓ`. Since characters of a split torus are determined by their
  functionals, `rootMult_eval` gives `rootMult (eval T γ) = finrank (weightSpace t γ)`, which is
  positive for a root (`finrank_weightSpace_pos`).
- `torusData` takes a split torus `t : T ⟶ G`, a homomorphism `g : A₁ ⟶ T` whose real cocharacter
  map is injective with image the common kernel of the roots vanishing on it, integral coroots
  whose reflections permute the roots and preserve the dimensions of their weight spaces (the
  conclusions of `LeviSplitComponentRootDatumStatement`), complementary subspaces `B`, `K'` of
  `V A₁`, and the fibre-sum condition: for every root `γ` with nonzero restriction to `B`, the sum
  over the roots `δ` with the same restriction to `B` of `finrank (weightSpace t δ) · δ(g y)`
  vanishes for `y ∈ K'`. It returns `FieldDescentData (V A₁) (V T)` with `κ = cocharacterMapReal g`,
  roots `rootFunctionals hT t`, multiplicities `rootMult hT t`, coroots `1 ⊗ γv`, and `B`, `K'`.
