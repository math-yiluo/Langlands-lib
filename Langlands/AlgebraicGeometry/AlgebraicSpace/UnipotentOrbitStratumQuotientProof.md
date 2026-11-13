# The quotient of an orbit-dimension stratum: proof

Authors: Worker 79 and Worker 5217.

This module proves `Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStratumQuotientStatement.{u}`,
the second clause of Conrad's Example 5.5 (printed p.16). The theorem is
`Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStratumQuotient`.

The setting: a unipotent algebraic group `G` over a henselian valued field `K` of
characteristic zero acts by `a` on a reduced `K`-scheme `V` of finite type. Fix `d : ℕ`
and an immersion `i : Z → V` from a reduced scheme onto the points of orbit dimension
`d`. The theorem gives an action `b` of `G` on `Z` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom`,
whose stabilizer is flat over `Z` (`IsStabilizerFlat b`). It also gives an algebraic space
`X` over `Spec K` with a map `π` from the sheaf of `Z`. Here `π` is an fppf quotient of `Z`
by `b`, flat and surjective, and `X` is quasi-separated and of finite presentation over `K`.

## Published inputs

The proof is a direct assembly of results already proved in the Library:

- `Langlands.GroupScheme.affineCartierSmooth : AffineCartierSmoothStatement.{u}`
  (Cartier's theorem, Milne, *Algebraic Groups*, Theorem 3.23): an affine group scheme
  locally of finite type over a field of characteristic zero is smooth.
- `orbitStratumActionRestriction : OrbitStratumActionRestrictionStatement.{u}`: for `G`
  smooth over a field `k`, `V` locally of finite type, and an immersion `i : Z → V`
  as above, some action `b` on `Z` makes `i` equivariant. Every such `b` has
  `HasOrbitDimension b z d` at every point `z` of `Z`.
- `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected`, applied to
  `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` (SGA 3, Exposé VI_B,
  Corollaire 4.4, over a reduced locally Noetherian base, with connected fibres) and to
  `Langlands.GroupScheme.charZeroUnipotentConnected` (Milne, Corollary 14.15: unipotent
  groups in characteristic zero are connected). Together they prove
  `UnipotentOrbitStabilizerSmoothStatement.{u}`. If `G` is unipotent, affine and locally
  of finite type over a field of characteristic zero, `Z` is reduced and locally of finite
  type, and an action `b` on `Z` has constant orbit dimension `d`, then the stabilizer
  projection `(pullback.snd (lift b.hom (snd G.X Z)) (lift (𝟙 Z) (𝟙 Z))).left` is smooth.
- `smoothStabilizerActionQuotient : SmoothStabilizerActionQuotientStatement.{u}`: let `G`
  be smooth over a scheme `S`, let `V` be locally of finite type over `S`, and let the
  stabilizer of an action be smooth. Then an fppf quotient `π` of `V` by the action exists
  in algebraic spaces over `S`. Every such quotient `π` is smooth and surjective
  (`IsSmooth π.hom`, `IsSurjective π.hom`), and its target is locally of finite type over
  `S`.
- `actionQuotientFiniteness : ActionQuotientFinitenessStatement.{u}`: let `G` be
  quasi-compact over a field `k` and let `Z` be locally of finite type and quasi-compact
  over `k`. Then every smooth surjective fppf quotient `X` of `Z` that is locally of finite
  type is quasi-separated and of finite presentation over `k`.

## The argument

Let `hG : IsUnipotentAlgebraicGroup K G`, so `hG.1 : IsAffineHom G.X.hom`,
`hG.2.1 : LocallyOfFiniteType G.X.hom` and `hG.2.2 : IsUnipotent G`. Let
`hV : IsReducedFiniteType K V`.

1. The proof first records `hB : UnipotentOrbitStabilizerSmoothStatement.{u}` as the
   reduction applied to `reducedBaseConnectedFibreSmooth` and
   `charZeroUnipotentConnected`.
2. Cartier's theorem, from `hG.1`, `hG.2.1` and `CharZero K`, gives `Smooth G.X.hom`.
3. `Z` is locally of finite type over `K`: its structure morphism is `i.left ≫ V.hom`
   (`Over.w i`), and an immersion is locally of finite type.
4. `Z` is quasi-compact over `K`. `V` is locally Noetherian, because it is locally of
   finite type over a field. It is also quasi-compact, so it is a Noetherian scheme and its
   underlying space is Noetherian. The immersion `i.left` is a topological embedding, so the
   space of `Z` is Noetherian, hence compact. A morphism from a compact source to an affine
   target is quasi-compact.
5. `orbitStratumActionRestriction` gives `b` with `hb : b.hom ≫ i = (G.X ◁ i) ≫ a.hom`
   and constant orbit dimension `d` for `b` on `Z`.
6. `hB` applied to `G`, `Z` (reduced and locally of finite type), `b` and `d` gives a
   smooth stabilizer projection for `b`.
7. `smoothStabilizerActionQuotient` over `S = Spec K` gives an fppf quotient
   `π : Z → X`. Applied again to that quotient, it shows that `π` is smooth and
   surjective and that `X` is locally of finite type over `Spec K`.
8. `G.X.hom` is quasi-compact, because it is affine. `actionQuotientFiniteness` therefore
   shows that `X` is quasi-separated and of finite presentation over `K`.
9. `IsFlat π.hom` follows from `IsSmooth π.hom` by `MorphismProperty.relative_monotone`.
   Every represented projection of `π` is a smooth scheme morphism, hence flat.
10. `IsStabilizerFlat b` unfolds to `Flat` of the stabilizer projection, and a smooth
    morphism is flat.

The witnesses are `b`, `hb`, the flat stabilizer, `X`, `π`, the quotient property,
quasi-separatedness, finite presentation, flatness and surjectivity of `π`.

## Relation to the source

Conrad states that the fppf quotient `V_d/G` is an algebraic space of finite presentation
receiving a faithfully flat map from `V_d`. He uses quotients by flat groupoids locally of
finite presentation ([Del2, Prop. 3.11]; Stacks, Theorem 80.10.1, Tag 04S6). In this proof
the stabilizer is shown to be smooth, not merely flat, through SGA 3 VI_B 4.4 and Cartier's
theorem. The existence and smoothness of the quotient then come from the published
`smoothStabilizerActionQuotient`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
