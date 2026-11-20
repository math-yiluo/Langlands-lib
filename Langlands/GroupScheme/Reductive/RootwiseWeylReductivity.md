# Reductivity from rootwise Weyl inversions

Author: Worker 5397. The interface was proposed by Worker 163 for Task 7827 (Borel–Tits 1965,
Théorème 7.2). It is an internal support module: it combines two published
reductivity criteria and asserts no new source theorem.

Throughout, `K : Type u` is a field and `G` is a group scheme over `Spec K`. `T` is a
commutative group scheme over `Spec K`, and `i : T.toGrp ⟶ G` is a homomorphism. For a
character `α` and a cocharacter `ν` of `T`, `⟨α, ν⟩` is `latticePairing T α ν`. Also:

- `roots i` is the set of nonzero characters with nonzero weight space in the Lie algebra
  `lieKernel G K`.
- `weightSpace i α` is that weight space.
- `torusCentralizer i` is the subgroup functor of points that commute with the image of
  `i` on every test scheme.

## Weyl inversions

`IsWeylInversion i α c n` takes an automorphism `c : T.toGrp ≅ T.toGrp` and a point
`n : Lie.AffinePoints G K` (a `K`-point of `G`, in the coefficient-point convention of the
published `RankOneWeylReductivityStatement`). It says three things:

1. `c.hom ≫ α = -α` as homomorphisms to `𝔾_m`, so `c` inverts the character `α`;
2. `ν ≫ c.hom = ν` for every cocharacter `ν` with `⟨α, ν⟩ = 0`, so `c` fixes the
   cocharacters orthogonal to `α`;
3. `PointwiseSchemeAction.IsTransporter (c.hom ≫ i) i n`: on every test scheme,
   `i(c(x)) · n = n · i(x)`, so conjugation by `n` restricts to `c` on the torus.

A reflection `s_α` of a root datum has these properties. It acts on cocharacters by
`ν ↦ ν - ⟨α, ν⟩ α^∨`, which fixes the orthogonal complement of `α`.

`IsWeylInversion.map_weightSpace` shows that the differential of conjugation by `n` carries
`weightSpace i α` onto `weightSpace i (-α)`. It uses the published transport lemma
`weightSpace_map_of_transport`, together with `RankOneWeylCriterion.comp_innerIso_hom_of_isTransporter`
and `RankOneWeylCriterion.commIso`. That differential is injective, so
`IsWeylInversion.neg_mem_roots` follows: if `α` is a root then so is `-α`, with the same
`finrank`.

## The centralizer of a root-orthogonal cocharacter

`exists_orthogonalCocharacter` works for `G` affine and locally of finite type and `T` a
split torus. For `α ≠ 0` it gives `ζ` with `⟨α, ζ⟩ = 0` such that every root `β` with
`⟨β, ζ⟩ = 0` satisfies `m • β = n • α` for some integers `m ≠ 0` and `n`. The proof first
picks `ν` with `⟨α, ν⟩ ≠ 0` (`IsSplitTorus.exists_pairings_ne_zero`), then applies the
published `IsSplitTorus.exists_rootOrthogonalCocharacter`, which gives
`⟨α, ν⟩ • β = ⟨β, ν⟩ • α`.

Let `m : M ⟶ G` represent `Dynamic.centralizer (ζ ≫ i)`, and let `t : T ⟶ M` satisfy
`t ≫ m = i`.

- `pairing_eq_zero_of_mem_roots` (`G` smooth affine): every root `β` of `t` has
  `⟨β, ζ⟩ = 0`. A nonzero weight vector of `M` maps under the injective differential of `m`
  to a weight vector of `G`. That vector lies in the Lie algebra of the centralizer, which
  by the published `dynamicLie` is the weight-zero space of `ζ`. Its `ζ`-weight is
  `⟨β, ζ⟩`, so `⟨β, ζ⟩ = 0` by `weightSpace_disjoint`. This is the argument of the
  published `dynamicCentralizerRoots`, without its reductivity hypotheses.
- `IsWeylInversion.exists_lift`: if `⟨α, ζ⟩ = 0`, a Weyl inversion `(c, n)` of `α` gives a
  point `n'` of `M` with `IsTransporter (c.hom ≫ t) t n'`. Since `c` fixes `ζ`, conjugation
  by `n` commutes with `ζ ≫ i`, so `n` lies in the centralizer and factors through `m`. The
  transporter identity descends along the monomorphism `m`.

`isConnectedReductive_centralizer` is the main step. It assumes:

- `K` is algebraically closed, and `G` is smooth, affine and connected;
- `T` is split, `i` is closed, and `torusCentralizer i = range i`;
- every root space is a line;
- the roots are reduced: if roots `α`, `β` satisfy `m • β = n • α` with `m ≠ 0`, then
  `β = ±α`;
- `α` is a root with a Weyl inversion `(c, n)`;
- `ζ` is as in `exists_orthogonalCocharacter`;
- `m : M ⟶ G` is a closed representative of the centralizer of `ζ ≫ i`.

It concludes that `M` is connected reductive. The proof proceeds as follows.

1. `M` is smooth and connected, by the published `dynamicSmooth` and
   `DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer`.
2. The torus factors as `t` with `t ≫ m = i`, by `range_le_centralizer_groupHom_comp` and
   `IsRepresentedBy.liftOfLE`. Then `t` is a closed split subtorus
   (`IsClosedSubgroup.of_comp`).
3. `t` is self-centralizing, by `RelativeRoot.torusCentralizer_eq_range_of_comp_mono`.
4. `roots t = {α, -α}`. A root of `t` is a root of `i` (`roots_subset_comp`) that is
   orthogonal to `ζ`, so it is proportional to `α`, hence `±α` by reducedness. Conversely,
   `α` and `-α` are roots of `i` orthogonal to `ζ`, so they are roots of `t` by the
   published `mem_relativeRoots_of_pairing_eq_zero`.
5. Both root spaces of `t` are lines: the published `map_weightSpace_of_pairing_eq_zero`
   identifies them, via the injective differential of `m`, with those of `i`.
6. `IsWeylInversion.exists_lift` supplies the Weyl point in `M`. The published
   `rankOneWeylReductivity` then gives connected reductivity of `M`.

## The criterion

`rootCentralizerData` is the entry definition. It takes the hypotheses of the criterion, a
root `α` and a Weyl inversion of `α`. It produces the published structure
`RadicalFreeRootCentralizerData i α`:

- the cocharacter is the chosen `ζ`;
- the group is the fixed affine representative `Dynamic.Affine.centralizerScheme (ζ ≫ i)`,
  with its closed inclusion `Dynamic.Affine.centralizerHom`;
- `⟨α, ζ⟩ = 0`;
- the trivial unipotent radical comes from `isConnectedReductive_centralizer` and
  `IsConnectedReductive.hasTrivialUnipotentRadical`.

`isConnectedReductive_of_rootwiseWeyl` is the main theorem. Let `K` be algebraically closed
and `G` smooth, affine and connected. Let `i : T ⟶ G` be a closed split torus with
`torusCentralizer i = range i`. Assume that every root space is a line, the roots are
reduced in the sense above, and every root `α` has a Weyl inversion (the three clauses of
`IsWeylInversion`, spelled out). Then `G` is connected reductive. The proof applies the
published `RadicalFreeRootCentralizerData.isConnectedReductive` to `rootCentralizerData`.

## Provenance

This is an internal composition of published Library results: the rank-one Weyl criterion
(`Reductive.RankOneWeylCriterionProof`), the rootwise centralizer criterion
(`Reductive.FiniteCentralizerNeighbourhood`), and the root-orthogonal centralizer lemmas
(`Rational.RootOrthogonalCentralizer`). The underlying mathematics is the standard reduction
of reductivity to the centralizers of codimension-one subtori. Each such centralizer has
semisimple rank at most one, and in rank one a Weyl element excludes a unipotent radical. No
hypothesis beyond those displayed is used, and the field may have any characteristic.
