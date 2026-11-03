# Dominant homomorphisms onto reduced groups are flat

This module proves, over an arbitrary field `k`, the flatness half of Milne's
homomorphism theorem for group schemes (Milne, *Algebraic Groups*, Proposition 1.70
and Summary 1.71, printed p.28): a dominant homomorphism onto a reduced group is
flat. It also proves that a flat homomorphism onto an irreducible group is
surjective. Milne works over an algebraically closed field and uses transitivity of
the action on rational points. The Lean proofs use generic flatness instead and
translate by families of points, so they need no hypothesis on `k`.

## Declarations

- `RingHom.Flat.of_comp_faithfullyFlat`: if `g : S →+* T` is faithfully flat and
  `g.comp f` is flat, then `f : R →+* S` is flat. The proof base-changes an
  injective `R`-linear map to `S`. It then uses that `T ⊗_S (S ⊗_R -)` is
  `T ⊗_R -` (`AlgebraTensorModule.cancelBaseChange`), and that `T` reflects
  injectivity over `S`.
- `flat_stalkMap_of_flatNear`: if a morphism is flat on an affine neighbourhood of
  `z` (the published `OrbitMapFlat.FlatNear`), then its stalk map at `z` is flat.
- `flat_stalkMap_of_comm`: take a commutative square `f' ≫ g = g' ≫ f` in which
  `g` and `g'` are flat. If the stalk map of `f'` at `z` is flat, then the stalk map
  of `f` at `g' z` is flat. The stalk map of `g'` is a flat local homomorphism, hence
  faithfully flat, so the previous ring lemma applies.
- `shearLeft u`, `shearRight u`: for a group object `G` and `u : T ⟶ G` in a
  cartesian monoidal category, the automorphisms `(t, x) ↦ (t, u t * x)` of
  `T ⊗ G` and `(x, t) ↦ (x * u t, t)` of `G ⊗ T`. The lemmas
  `shearLeft_hom_snd` and `shearRight_hom_fst` give their relevant coordinates.
- `flat_mul_left`, `flat_mul_right`, `surjective_mul_left`: for a group object
  `G` over `S` and `u : T ⟶ G`, the translation maps `(t, x) ↦ u t * x` and
  `(x, t) ↦ x * u t` are flat when `T` is flat over `S`. The first one is surjective
  when `T` is surjective over `S`. Each map is a shear followed by a projection.
- `flat_of_isDominant`: let `f : A ⟶ B` be a homomorphism of group schemes over
  `Spec k` whose underlying morphism is locally of finite type, quasi-compact and
  dominant, with `B` reduced and locally noetherian. Then `f` is flat.
- `surjective_of_flat`: a homomorphism `f : A ⟶ B` of group schemes over `Spec k`
  with flat underlying morphism and irreducible `B` is surjective.

## Proofs

`flat_of_isDominant`. Fix a point `x` of `A`. Generic flatness
(`OrbitMapFlat.exists_open_flatNear`, published) gives a nonempty open `U` of `B`
on which `f` is flat near every point of `f ⁻¹ U`. Dominance gives a point `w` with
`f w ∈ U`. So `W := f ⁻¹ U` is a nonempty open of `A`, and `W ↪ A ⟶ B` is
flat. `W` is surjective over `Spec k`, because `Spec k` has one point. Consider
the square

    W ⊗ A  --(ι ≫ f) ▷ A-->  B ⊗ A
      |                        |
      | (w, a) ↦ w * a         | (b, a) ↦ b * f a
      v                        v
      A    --------f------->   B

The top map is a base change of a flat map. The vertical maps are flat by
`flat_mul_left` and `flat_mul_right`, and the left one is surjective by
`surjective_mul_left`. Choose a preimage `z` of `x` under the left map. The stalk of
the top map at `z` is flat, so `flat_stalkMap_of_comm` gives flatness of `f` at
`x`.

`surjective_of_flat`. Let `b` be a point of `B` and `T = Spec κ(b)` with its
canonical point `t_b : T ⟶ B`. The map `α : T ⊗ A ⟶ B`, `(t, a) ↦ t_b t * f a`,
is flat: it is `T ◁ f` followed by a left translation. Flat morphisms are
generizing, and `B` is irreducible, so the generic point of `B` lies in the range
of `α` and in the range of `f`. A point `z` of the fibre product of `α` and `f`
over that generic point exists. On the fibre product,
`t_b ∘ pr = (p₂ * (p₁ ≫ snd)⁻¹) ≫ f`. Evaluating at `z` gives a point of `A`
that maps to `b`.

## Provenance

The statements are those of Milne Proposition 1.70 and Corollary 1.69 (via Summary
1.71), adapted to group schemes over an arbitrary field in the Library's
`GroupScheme (Spec k)` setting. Flatness assumes `f` locally of finite type and
quasi-compact, and `B` locally noetherian. Surjectivity assumes `f` flat and `B`
irreducible, instead of dominance. The Lean proofs are the internal routes described
above. They are a helper for the image of a homomorphism used in the split
unipotent radical existence proof.
