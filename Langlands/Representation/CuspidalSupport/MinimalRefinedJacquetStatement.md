# Minimal nonzero refined Jacquet descent in a product Levi

Author: Worker 379.

This pair states one future proof target in `Langlands.CuspidalSupport`. It
is a proposition definition only. It does not prove the assertion, does not
assume it anywhere, and claims no Library result implies it. Worker 320
requested it as an input for admissibility of arbitrary irreducible
product-Levi representations.

## Exact declaration

`Langlands.CuspidalSupport.MinimalNonzeroRefinedJacquetTheorem.{uF,uV} F T`
has outer binders
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
Its body installs exactly `T.topology` on `F.Carrier` and then asserts:

> for every `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
> `A : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, if `Nontrivial A` then
> there is `S : BlockRefinement B` such that
>
> 1. `Nontrivial (RefinedJacquetModule B S A.representation)`, and
> 2. `IsLeviQuasicuspidal (B.flatten S) ((T.normalizedRefinedJacquet B S
>    A.representation).comp e.toMonoidHom)`,
>
> where `e` is the group equivalence displayed below.

In Lean, `e` is written inline in clause 2. It is

```
e := GeneralLinear.BlockShape.leviRefinementEquiv
  (B.flatten S) B S (B.flattenBlockEquiv S)
  (fun q => (B.flatten_size_flattenBlockEquiv S q).symm)
  F.Carrier
```

All of `n`, `B` and `A` are universally quantified inside the proposition;
`F` and `T` are parameters. `S` is existential. The statement does not claim
that `S` is unique or maximal, and it adds no other minimality witness.

## The objects involved

All names below are existing Library declarations, reused by name.

- `B.Levi F.Carrier` (`Langlands.Group.GL.Blocks`) is the actual product
  `∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier`. Its topology is
  the inferred product of the matrix topologies induced by `T.topology`.
  This is the same instance as `T.leviTopology B`, and no other topology
  is chosen. `SmoothRep.{0,uF,uV} ℂ G` is the full subcategory of `Rep ℂ G`
  whose objects are smooth. Smoothness is thus part of the input object.
  `Nontrivial A` says that the complex carrier of `A` is nonzero.
- `BlockRefinement B` (`Geometric.WeylDefinitions`) is
  `∀ i : Fin B.length, BlockShape (B.size i)`. It gives an ordered
  partition of every outer block into positive inner blocks. The subgroups
  `refinedParabolic`, `refinedLevi` and `refinedUnipotent` of `B.Levi R`
  are the products over `i` of the upper block parabolic, the block
  diagonal Levi and the upper block unipotent subgroup of `S i`.
- `Geometric.RefinedJacquetModule B S A.representation`
  (`Geometric.RefinementFunctors`) is literally
  `Jacquet.Coinvariants A.representation (refinedUnipotent F.Carrier B S)`.
  It is the quotient of the whole carrier of `A` by the span of the vectors
  `A(u)v - v` with `u` in the refined unipotent radical. Clause 1 concerns
  this entire quotient. No irreducible quotient, constituent or other
  subquotient is chosen. The quotient has the same carrier universe `uV` as
  `A`.
- `T.normalizedRefinedJacquet B S A.representation` is the action of
  `refinedLevi F.Carrier B S` on that same quotient. By
  `normalizedRefinedJacquet_mk` it acts on a class by
  `m [v] = T.refinedLeviInverseHalfModulus B S m • [A(m.val) v]`. The full
  character `T.refinedLeviModulus B S` is the product over the outer blocks
  `i` of `T.leviModulus (S i)` evaluated on the inner coordinates of `m`.
  This is the modulus of the refined unipotent radical, and the factor is
  its canonical positive inverse square root. The Library's
  `T.normalizedRefinedInduced B S` uses the positive half
  `T.refinedLeviHalfModulus B S` of the same character. Its functions
  satisfy the covariance `f(q g) = χ(projection q) • σ(projection q)(f g)`
  with `χ` the inflated half modulus, and the group acts by right
  translation. The pair of conventions therefore matches BZ77 1.8.
- `IsLeviQuasicuspidal C ρ` (`CuspidalSupport.LeviDefinitions`) says that
  for every `S' : BlockRefinement C` with `refinedParabolic F C S' ≠ ⊤`,
  the coinvariants `Jacquet.Coinvariants ρ (refinedUnipotent F C S')` form
  a subsingleton. It requires neither smoothness nor admissibility.

### The coordinate pullback `e`

`B.flatten S` (`MinimalJacquetProof`) is the block shape of rank `n` whose
blocks are the inner blocks of `S 0`, then those of `S 1`, and so on. The
flattened block number `B.flattenBlockEquiv S ⟨i, k⟩` is `finSigmaFinEquiv`
of `⟨i, k⟩`, and `B.flatten_size_flattenBlockEquiv S` proves that its size
is `(S i).size k`. `leviRefinementEquiv`
(`Langlands.Group.GL.RefinementCoordinates`) takes a target shape, an outer
shape, a refinement, an indexing equivalence and size equations. Here these
are `B.flatten S`, `B`, `S`, `B.flattenBlockEquiv S`, and the reversed size
equations. The result is a multiplicative equivalence

`e : (B.flatten S).Levi F.Carrier ≃* refinedLevi F.Carrier B S`

with the flattened Levi as source and the subgroup-valued refined Levi as
target. A private check confirmed this type and the coordinate formula

`(e m).val i = (S i).leviEmbedding F.Carrier
  (fun k => reindex (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, k⟩))
    (m (B.flattenBlockEquiv S ⟨i, k⟩)))`

by `rfl`. Thus the `k`-th inner diagonal block of outer block `i` of `e m`
is the flattened block number `flattenBlockEquiv ⟨i, k⟩` of `m`, with the
matrix indices cast along the proved size equation. Clause 2 composes the
normalized action with `e.toMonoidHom`. The result is a representation of
`(B.flatten S).Levi F.Carrier` on the same quotient carrier, so the
refinements tested by `IsLeviQuasicuspidal (B.flatten S)` are refinements
of the flattened shape. The statement does not assume that this transport
preserves or reflects quasicuspidality. It does not substitute a tensor
factorization, a separately chosen representation, or a label for this
action.

On an element `u` of a refined unipotent subgroup of the flattened Levi,
every diagonal block of `e u` has determinant one. Each block modulus is a
product of powers of absolute values of block determinants, so it takes the
value one on `e u`. The normalization factor is therefore one on these
elements, and the coinvariants tested in clause 2 are those of the
unnormalized pulled-back action. This remark explains why normalized and
unnormalized quasicuspidality agree; it is not proved in this pair.

## Universes

`uF` is the universe of the field carrier, so `B.Levi F.Carrier` and
`refinedLevi F.Carrier B S` lie in `Type uF`. The coefficient field `ℂ` is
in `Type 0`, the first universe argument of `SmoothRep`. `uV` is the carrier
universe of `A`. It is an independent universe parameter, with no relation
imposed to `uF`. The quotient `RefinedJacquetModule B S A.representation` is
a quotient of the carrier of `A`, so it also lies in `Type uV`.

Consumers whose carriers live in the saturated universe, such as carriers of
parabolic induction from a `uV` carrier, use the specialization
`MinimalNonzeroRefinedJacquetTheorem.{uF, max uF uV} F T`. A private check
elaborated this specialization together with `{uF, uF}` and `{uF, 0}`.

## Included boundary cases

There is no hypothesis on `n`, `B`, `A` or `T` besides the ones displayed.
In particular there is no assumption of irreducibility, admissibility,
finite generation, finite length, finite dimension, a central character,
positive rank, a tensor factorization along the blocks, an embedding into
an induced representation, or a preselected nonzero refinement. There are no
theorem-valued parameters and no transitivity data.

- **Whole-product refinement.** `S` may be the refinement in which every
  `S i` has a single block. Then the refined parabolic is all of
  `B.Levi F.Carrier`, the radical is trivial, the quotient is a copy of the
  carrier of `A`, and the inverse half modulus is one. `B.flatten S` then
  has the same block sizes as `B`. This is the witness when `A` is already
  quasicuspidal.
- **Rank zero and the empty shape.** For `n = 0`, positivity of the block
  sizes and `∑ i, B.size i = 0` force `B.length = 0`. The only refinement is
  the empty family, `B.flatten S` is again empty, and `B.Levi F.Carrier` is
  the one-element group. The radical is trivial, so the quotient is a copy
  of the nonzero carrier of `A`. Every refinement of the empty flattened
  shape has the whole group as refined parabolic, so quasicuspidality holds
  vacuously. The statement therefore needs no positivity hypothesis. This
  elementary argument is internal derived content. It is not quoted from
  the source, and this pair does not formalize it.

## Original source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups. I*, Annales scientifiques de l'Ecole Normale Superieure (4)
10 (1977), 441–472. Literature ID: `bernstein-zelevinsky-1977-induced-i`.
PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Readable original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Page references give the printed page and the one-based PDF page.

The passages below were read directly on 2026-10-27. The formulas of 1.8
were read from the rendered page, since the PDF text layer drops the
minus sign of an exponent.

- **1.7–1.8**, printed p.444 / PDF p.5. `mod_U(g)` is the module of the
  automorphism `u ↦ g u g⁻¹`. Induction 1.8(a)(1) uses
  `f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))` with right translation. The
  localisation 1.8(b) is the quotient `E/E(U, θ)`, spanned by
  `π(u)ξ - θ(u)ξ`. On it, `M` acts by
  `δ(m)(ξ + E(U, θ)) = mod_U^{-1/2}(m)·(π(m)ξ + E(U, θ))`.
- **1.9**, printed p.445 / PDF p.6. Exactness, adjunction and the
  composition rule 1.9(c) for `i` and `r`. The text remarks that the
  `mod^{1/2}` factors are compatible.
- **2.1**, printed p.446 / PDF p.7. `G` is a connected reductive group
  with fixed minimal parabolic `P_0` and maximal split torus `A_0`. A
  standard subgroup `M < G` is the Levi subgroup containing `A_0` of a
  parabolic `P ⊇ P_0`. "In any standard subgroup `M < G` we fix the minimal
  parabolic subgroup `P_0 ∩ M` and the maximal split torus `A_0`. It is
  clear that `N < M` implies `N < G`."
- **2.2**, same page. For `GL(n, F)` with upper triangular `P_0` and
  diagonal `A_0`, the standard subgroups are numbered by ordered partitions
  `α = (n_1, …, n_r)` of `n`. They are `G_α = G_{n_1} × … × G_{n_r}`,
  embedded as block-diagonal matrices. Moreover `G_β < G_α` iff `β` is a
  subpartition of `α`.
- **2.3(c) and 2.4**, same page. Normalized transitivity
  `r_{N,M} ∘ r_{M,G} = r_{N,G}` for `N < M < G`. A representation is
  quasicuspidal if `r_{M,G}(π) = 0` for every standard `M ≠ G`.
- **2.14(1), first assertion**, printed p.449 / PDF p.10. "If
  `π_0 ∈ Alg G`, `π_0 ≠ 0`, then in accordance to 2.3 (c) there exists
  such a subgroup `L < G`, that `r_{L,G}(π_0)` is quasicuspidal and
  non-zero." The rest of 2.14 assumes that `π_0` is a subquotient of a
  particular induced representation. That part is not used.

No erratum or correction for this source was found. The search covered the
project literature folder and the central library listing on 2026-10-27.

### Correspondence

- **The group.** The source's `G` becomes the product Levi
  `B.Levi F.Carrier`, the `G_α` of 2.2 for the partition given by `B`. It is
  a connected reductive group. Its minimal parabolic is `P_0 ∩ G_α`, the
  product of the upper triangular groups, and its split torus is the
  diagonal torus, as fixed in 2.1. The field is a finite extension of
  `ℚ_p` with arbitrary supplied topological data, so it is a special case
  of the locally compact non-Archimedean fields of 2.1.
- **Standard subgroups and block refinements.** By 2.1 and 2.2, the
  standard subgroups of `G_α` are the `G_β` for subpartitions `β` of `α`.
  A subpartition of `α` is the same as an ordered partition of every part
  `n_i`, which is a `BlockRefinement B`. The corresponding parabolic and
  unipotent radical inside `G_α` are the intersections with `G_α` of those
  of `G_β` in `GL_n`, namely the products of the inner block subgroups.
  These are `refinedParabolic`, `refinedLevi` and `refinedUnipotent`. This
  identification is derived from 2.1–2.2 and is not quoted. The whole group
  `M = G` corresponds to the whole-product refinement.
- **The functor.** `r_{L,G}` of 2.3 is `r_{U,1}` of 1.8(b) for the
  radical `U` of `L`. Here `L` is `refinedLevi`, `U` is `refinedUnipotent`,
  and the character `θ` is trivial. The coinvariant module is the
  localisation `E/E(U, 1)`. The factor `mod_U^{-1/2}` is the inverse half of
  `T.refinedLeviModulus B S`. Indeed, the conjugation module of the upper
  block radical is `∏_{i<j} |det m_i|^{n_j} / |det m_j|^{n_i}`, which is the
  form of `T.leviModulus`.
- **Quasicuspidality of `r_{L,G}(π_0)` as a representation of `L`.** By
  2.1, the standard subgroups of `L = G_β` are those of `G_β` itself, the
  product over the flattened partition. The equivalence `e` identifies
  `G_β` with the Levi of the flattened shape. The flattened order is
  lexicographic: outer block first, then inner block. So `e` carries the
  upper triangular matrices of `(B.flatten S).Levi` to `P_0 ∩ L`, and
  standard subgroups to standard subgroups. Quasicuspidality of
  `r_{L,G}(π_0)` in 2.4 is therefore expressed by `IsLeviQuasicuspidal
  (B.flatten S)` of the action pulled back along `e`.
- **The category.** The source's `Alg G` (1.2) consists of complex
  representations with open vector stabilizers. This is `SmoothRep ℂ G`.
  The carrier universe `uV` is unrestricted, as the source places no
  cardinality condition on the representation space.

The rank-zero case is an elementary extension, explained above. The
source does not discuss `GL_0`.

## Relation to existing declarations

- `MinimalNonzeroJacquetTheorem` in
  `CuspidalSupport.MinimalJacquetStatement`, proved as
  `CuspidalSupport.minimalNonzeroJacquet`, has inputs that are smooth
  representations of `GeneralLinear n F.Carrier`. A representation of
  `B.Levi F.Carrier` is not such an input, not even for a one-block shape,
  whose Levi is a different Lean type. That theorem therefore does not
  supply this statement.
- `Langlands.Parabolic.NormalizedRefinementJacquetTransitivityClause` in
  `Parabolic.RefinementTransitivityStatement` concerns a `GL_n` input and
  the subgroup-valued `refinedLevi`. It is a separate statement target, and
  this pair does not use it as an input.
- `GeneralLinear.BlockShape.composeRefinement` and
  `flatten_composeRefinement` in `Group.GL.NestedRefinement` compose a
  refinement of `B.flatten S` with `S` into a refinement of `B`, with ordered
  block, size and index casts. They give the combinatorics a proof needs.
  They do not provide the action transport or the quotient comparison.

## Remaining proof obligations

A proof of this target is a separate task. Following 2.14(1) and 2.3(c),
one possible route is to choose, among the finitely many refinements with a
nonzero refined Jacquet quotient, one whose flattened shape has maximal
length. The whole-product refinement shows that such refinements exist. If
a proper refinement `S'` of `B.flatten S` gave nonzero coinvariants of the
pulled-back action, the following comparison would give a contradiction.
The iterated quotient is a quotient of the refined Jacquet module of `A` for
the composed refinement `B.composeRefinement S S'`. By
`flatten_composeRefinement`, the flattened shape of that refinement is
`(B.flatten S).flatten S'`, which is longer than `B.flatten S`. So the
composed refinement would have a nonzero quotient and a longer flattened
shape. That proof would need:

- the identification of the coinvariants of the pulled-back action, for
  `S'`, with a quotient of the refined Jacquet module of `A` for
  `composeRefinement`, compatibly with `flatten_composeRefinement`;
- the finiteness of block refinements and the existence of a maximal one;
- the whole-product and empty-shape identifications.

None of these is proved here. This pair proves no descent, transitivity,
quasicuspidal embedding, irreducible extraction or admissibility.
