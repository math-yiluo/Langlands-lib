# Root parametrizations of all roots by Weyl conjugation of the simple ones

Module `Langlands.GroupScheme.Reductive.LocalSplitWeylFamily`, namespace
`Langlands.GroupScheme.LocalSplitCell`.

## Setting

`R` is a commutative ring and `G`, `H` are group schemes over `Spec R`. `T_I = splitTorus (Spec R) I`
is the coordinate split torus. `Ga`, `rootPoint`, `weylPoint`, `IsRootParametrization` and
`IsWeylPoint` are as in the Library module `Langlands.GroupScheme.Reductive.LocalSplitCell`.
`P : RootDatum J (I → ℤ) (I → ℤ)` is a coordinate root datum with a base `b`.

## Transport results

- `charValue_comp_exponentIso_inv`: for a lattice automorphism `e`, the character with exponent
  `m`, evaluated at `t` moved by the inverse of `exponentIso e`, is the character with exponent
  `e.symm m` evaluated at `t`.
- `IsRootParametrization.comp_iso_of_exponentIso`: let `Φ : G ≅ H` and `e` satisfy
  `i ≫ Φ.hom = exponentIso e ≫ i'`. If `u` is a root parametrization of `i` for `m`, then
  `u ≫ Φ.hom` is a root parametrization of `i'` for `e.symm m`.
- `IsRootParametrization.comp_innerIso`: if `IsWeylPoint i n f`, then conjugating a root
  parametrization of `i` for `m` by `n` gives a root parametrization of `i` for `f.symm m`.

## Words and the Weyl family

- `wordReflect P [j₁, …, jₖ] m = s_{j₁}(⋯ (s_{jₖ} m))`, the reflections of `P` applied with the
  last letter first. `wordReflect_neg`: it commutes with negation.
- `SimpleWord P b α`: a simple root `simple ∈ b.support` and a word `word` of simple roots with
  `wordReflect P word (P.root simple) = P.root α`.
- `nonempty_simpleWord`: if `J` is finite and `P` is reduced, every root `α` has such a word.
- `rootWeylPoint P u a = weylPoint (u a) (u (P.reflectionPerm a a))`, that is
  `u_{-a}(-1) u_a(1) u_{-a}(-1)`. Mathlib's `P.reflectionPerm a a` is the index of the root
  `-P.root a`.
- `wordConj P u [j₁, …, jₖ] w = Ad(N_{j₁}) ∘ ⋯ ∘ Ad(N_{jₖ}) ∘ w` with `N_j = rootWeylPoint P u j`,
  where `Ad(N)` is the inner automorphism `G.innerIso N`.
- `weylFamily P W u α = wordConj P u (W α).word (u (W α).simple)`. Here `W` chooses one
  `SimpleWord` for each root. The same choice `W` is used for `G` and for `H`.

## Results on the Weyl family

- `isRootParametrization_wordConj` and `isRootParametrization_weylFamily`: assume each `u a`
  with `a` simple is a root parametrization of `i` for `P.root a`. Assume also
  `IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)` for every simple `a`. Then
  `weylFamily P W u α` is a root parametrization of `i` for `P.root α`, for every root `α`.
- `constantPoint_weylPoint`: on a test scheme `Z`, the pulled-back Weyl point is
  `u'_Z(-1) u_Z(1) u'_Z(-1)`.
- `map_constantPoint_rootWeylPoint`, `map_rootPoint_wordConj` and `map_rootPoint_weylFamily`:
  fix a test scheme `Z` over `Spec R` and a group homomorphism `Ψ : G(Z) → H(Z)` of points. Let
  `u` and `u'` be families of maps `Ga ⟶ G` and `Ga ⟶ H`. Suppose `Ψ (u_a(c)) = u'_a(c)` for
  every simple `a` and every `c`, and `Ψ (u_{-a}(-1)) = u'_{-a}(-1)` for every simple `a`. Then
  `Ψ` carries the value at `c` of `weylFamily P W u α` to the value at `c` of
  `weylFamily P W u' α`, for every root `α` and every `c`.

## Cell maps

- `map_orderedProduct`, `map_comp_cellMap`: let `Ψ : G(Z) → H(Z)` be a group homomorphism. Suppose
  it carries `t ≫ i` to `t ≫ i'` for every torus point `t`, and `u_α(c)` to `u'_α(c)` for every
  root `α` and every `c`. Then it carries `x ≫ cellMap i u neg pos` to
  `x ≫ cellMap i' u' neg pos` for every point `x` of the cell source, by the big-cell formula
  `comp_cellMap` of `LocalSplitCell`.
- `cellRelation_of_map`: under the same hypotheses, `(x ≫ j) * (y ≫ j) = c ≫ j` for
  `j = cellMap i u neg pos` implies the same relation for `ν = cellMap i' u' neg pos`. This is
  the relation in the Library's `CellGluing.CellCompatible`, at the single test scheme `Z`.

## Proof

`IsRootParametrization.comp_iso_of_exponentIso` checks the three fields. Representation:
`IsRepresentedBy.comp_iso` moves the represented functor along `Φ`. The Library lemma
`RelativeRoot.subgroup_comap_of_transport`, for the torus isomorphism `(exponentCommIso e).symm`
and `Φ.symm`, identifies the moved functor with the root subgroup functor of `i'` for
`e.symm m`. The character comparison is `exponentHom_comp_exponentCharacter`:
`exponentHom e ≫ χ_{e.symm m} = χ_m`. Closedness: `IsClosedSubgroup.comp_iso`. Equivariance: write
the point `t ≫ i'` as the image under `Φ` of `t' ≫ i`, where `t'` is `t` moved by the inverse
of `exponentIso e`. Then apply the equivariance of `u` at `t'` and
`charValue_comp_exponentIso_inv`. `IsRootParametrization.comp_innerIso` is the case
`Φ = G.innerIso n`. Here `IsWeylPoint.isNormalizingPoint` (module `LocalSplitRootTransport`)
supplies `i ≫ Ad(n) = exponentIso f ≫ i`.

`nonempty_simpleWord` is Mathlib's induction principle `RootPairing.Base.induction_reflect` for
roots, applied to the predicate "`α` has a simple word". This needs `J` finite, `P` reduced
and crystallographic (automatic over `ℤ`). The three cases are as follows. A simple root takes
the empty word. If `α = w(a)`, then `s_j(α)` takes the word `j :: w`. The negative
`-α = w(-a) = w(s_a(a))` takes the word `w ++ [a]`, by `wordReflect_neg` and
`reflection_apply_self`.

`isRootParametrization_wordConj` is an induction on the word using `comp_innerIso`. The
reflection `P.reflection j` is its own inverse, so the exponent `(P.reflection j).symm x` is
`P.reflection j x`. The weylFamily statement then rewrites with `root_eq` of the chosen word.

`map_rootPoint_wordConj` is an induction on the word. Conjugation by `N` on `Z`-points is
`x ↦ N_Z x N_Z⁻¹` (Library `GroupScheme.comp_innerIso_hom`). `Ψ` is multiplicative and carries
`N_Z` to `N'_Z` by `map_constantPoint_rootWeylPoint`. That lemma pulls the Weyl point back to
`Z` (`constantPoint_weylPoint`, from `comp_rootPoint`; pullback of global functions maps `±1`
to `±1`) and uses the hypotheses at `±1`.

`map_comp_cellMap` rewrites both sides with `comp_cellMap`. It then uses that `Ψ` is
multiplicative, so it maps the ordered list products factor by factor (`map_list_prod`).
`cellRelation_of_map` applies `Ψ` to the relation in `G`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. The construction
gives every root group a parametrization determined by the simple ones. It uses Weyl
conjugation, as in the description of a pinned split group by its simple-root data (Conrad,
*Reductive group schemes*, Cor. 5.1.9 for the Weyl points `w_a(1)`, PDF pp.140-141). Its
purpose is that an isomorphism respecting the simple-root data respects the parametrizations
of all root groups. The proofs combine the Library and Mathlib results named above and follow no
particular printed source.
