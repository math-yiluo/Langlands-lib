# Rational points of the quotient of an orbit-dimension stratum: proof

Authors: Worker 79 and Worker 5217.

This module proves `Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientPointTopologyStatement.{u}`,
the third clause of Conrad's Example 5.5 (printed p.16), corrected by assuming that the
quotient is locally separated. The theorem is
`Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitQuotientPointTopology`.

The setting: a unipotent algebraic group `G` over a henselian valued field `K` of
characteristic zero acts by `a` on a reduced `K`-scheme `V` of finite type. Fix `d : ℕ`,
an immersion `i : Z → V` from a reduced scheme onto the points of orbit dimension `d`,
and an action `b` of `G` on `Z` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom`. Let `X` be an
algebraic space over `Spec K` with a map `π` from the sheaf of `Z` that is an fppf quotient
of `Z` by `b`. If `X` is locally separated, then `HasLocallyHausdorffRationalPoints K X`
holds. Every rational point of `X` has an open neighbourhood, in the étale chart topology,
that is Hausdorff. That neighbourhood is locally compact if `K` is, and totally
disconnected if the norm of `K` is ultrametric.

## Published inputs

The proof is a direct assembly of results already proved in the Library:

- `Langlands.GroupScheme.affineCartierSmooth : AffineCartierSmoothStatement.{u}`
  (Cartier's theorem, Milne, *Algebraic Groups*, Theorem 3.23): an affine group scheme
  locally of finite type over a field of characteristic zero is smooth.
- `orbitStratumActionRestriction : OrbitStratumActionRestrictionStatement.{u}`: for `G`
  smooth over a field `k`, `V` locally of finite type, and an immersion `i : Z → V`
  as above, every action `b` on `Z` making `i` equivariant has
  `HasOrbitDimension b z d` at every point `z` of `Z`.
- `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected`, applied to
  `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth` (SGA 3, Exposé VI_B,
  Corollaire 4.4, over a reduced locally Noetherian base, with connected fibres) and to
  `Langlands.GroupScheme.charZeroUnipotentConnected` (Milne, Corollary 14.15: unipotent
  groups in characteristic zero are connected). Together they prove
  `UnipotentOrbitStabilizerSmoothStatement.{u}`. If `G` is unipotent, affine and locally
  of finite type over a field of characteristic zero, `Z` is reduced and locally of finite
  type, and an action `b` on `Z` has constant orbit dimension `d`, then the stabilizer
  projection of `b` is smooth.
- `smoothStabilizerActionQuotient : SmoothStabilizerActionQuotientStatement.{u}`: let `G`
  be smooth over `S`, let `Z` be locally of finite type over `S`, and let the stabilizer of
  the action be smooth. Then every fppf quotient `π` of `Z` by the action is smooth and
  surjective, and its target is locally of finite type over `S`.
- `actionQuotientFiniteness : ActionQuotientFinitenessStatement.{u}`: let `G` be
  quasi-compact over a field `k` and let `Z` be locally of finite type and quasi-compact
  over `k`. Then every smooth surjective fppf quotient `X` of `Z` that is locally of finite
  type is quasi-separated (and of finite presentation) over `k`.
- `locallySeparatedRationalPoints : LocallySeparatedRationalPointsStatement.{u}` (the
  topological claim of Example 5.5 for an arbitrary such space, not only an orbit
  quotient): over a henselian valued field `K`, every algebraic space `X` that is
  quasi-separated, locally separated and locally of finite type has
  `HasLocallyHausdorffRationalPoints K X`.

## The argument

Let `hG : IsUnipotentAlgebraicGroup K G` and `hV : IsReducedFiniteType K V`, and let
`hK : IsHenselianValuedField K`.

1. The proof first records `hB : UnipotentOrbitStabilizerSmoothStatement.{u}` as the
   reduction applied to `reducedBaseConnectedFibreSmooth` and
   `charZeroUnipotentConnected`.
2. Cartier's theorem, from `hG.1`, `hG.2.1` and `CharZero K`, gives `Smooth G.X.hom`.
3. `Z` is locally of finite type over `K`: its structure morphism is `i.left ≫ V.hom`
   (`Over.w i`), and an immersion is locally of finite type.
4. `Z` is quasi-compact over `K`. `V` is locally Noetherian, because it is locally of
   finite type over a field. It is also quasi-compact, so its underlying space is
   Noetherian. The immersion `i.left` is a topological embedding, so the space of `Z` is
   Noetherian, hence compact. A morphism from a compact source to an affine target is
   quasi-compact.
5. `orbitStratumActionRestriction` shows that the given action `b` has constant orbit
   dimension `d` on `Z`.
6. `hB` applied to `G`, `Z` (reduced and locally of finite type), `b` and `d` gives a
   smooth stabilizer projection for `b`.
7. `smoothStabilizerActionQuotient`, applied to the given quotient `π`, shows that `π` is
   smooth and surjective and that `X` is locally of finite type over `Spec K`.
8. `G.X.hom` is quasi-compact, because it is affine. `actionQuotientFiniteness` therefore
   shows that `X` is quasi-separated.
9. `X` is thus quasi-separated, locally of finite type and, by hypothesis, locally
   separated. `locallySeparatedRationalPoints` gives the conclusion.

## Relation to the source

Conrad asserts the topological properties of `(V_d/G)(K)` without assuming local
separatedness. The published statement adds this hypothesis, and its Markdown explains the
counterexample to the unqualified claim. It also qualifies local compactness and total
disconnectedness by the corresponding properties of `K`. The proof uses no further
hypothesis.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
