# Relative roots, the relative Weyl group and generic cocharacters

Author: Worker 1220.

This module continues the rational structure layer for group schemes over a
field. It is built on the split subtori of `Langlands.GroupScheme.Rational.SplitTorus`,
the torus centralizer of `Langlands.GroupScheme.Rational.TorusCentralizer`, and the
torus interface of `Langlands.GroupScheme.Torus.Weights` and
`Langlands.GroupScheme.Torus.Maximal` (`characterLattice`, `cocharacterLattice`,
`latticePairing`, `weightSpace`, `roots`, `normalizerPoints`,
`centralizerPoints`, `weylAction`). From these it defines the relative roots,
the relative Weyl group `N(k)/Z(k)`, the `ℚ`-span of the relative roots, the
action of the relative Weyl group on that span, and generic cocharacters. It
also proves the anisotropy consequences that need the character lattice and the
roots. All declarations are in the namespace `Langlands.GroupScheme`.
Throughout, `k : Type u` is a field, `S = Spec (CommRingCat.of k)`,
`T : CommGroupScheme S`, `G : GroupScheme S`, `i : T.toGrp ⟶ G`, and `G(k)`
means `Over.mk (𝟙 S) ⟶ G.X`.

## Sources

- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 5.1 (printed p.95, PDF p.42): « Les racines de G par rapport à S seront
    appelées k-racines ou racines relatives à k de G [...] Le groupe de Weyl
    relatif à k de G est le quotient N(S)/Z(S) [...] Il opère canoniquement sur
    X*(S) (en laissant ₖΦ stable) [...] donc aussi sur X*(S) ⊗ A [...] »
  - 5.3 (printed p.96, PDF p.43): « Chaque composante connexe de N(S)
    rencontre G_k. »
  - 4.15 (printed pp.90–91, PDF pp.37–38): the parabolics `G_{Φ⁺}`, `G_{Φ⁻}`
    with common Levi subgroup `Z(S)`.
- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - 25.13 (printed p.548, PDF p.564): "Under the adjoint action of S, the Lie
    algebra g of G decomposes into a direct sum g = g₀ ⊕ ⊕_{α ∈ X(S)} g_α [...]
    The characters α of S such that g_α ≠ 0 are called the relative roots of
    (G, S)."
  - 25.16 (printed p.549, PDF p.565): "Let ₖV be the subspace of X(S) ⊗ ℚ
    spanned by the relative roots of (G, S). The quotient N_G(S)/C_G(S) acts
    faithfully on S, and we identify it with its image in GL_{ₖV}."
  - 25.17 (printed p.549, PDF p.565): "The action of N_G(S) on ₖV factors
    through an isomorphism N_G(S)/C_G(S) → ₖW [...] Every coset of C_G(S) in
    N_G(S) is represented by an element of N_G(S)(k)."
  - 25.1 (printed p.544, PDF p.560): every parabolic subgroup is `P(λ)` for a
    cocharacter `λ`.
  - 25.6(b) and its proof (printed pp.545–546, PDF pp.561–562): the cocharacter
    `λ` of `S` can be chosen with `C_G(S) = C_G(λ(𝔾ₘ))`.

In both sources `G` is connected reductive and `S` is a maximal split torus.
The definitions below are stated for every `G` over `S` and every torus
homomorphism `i`; this generality is derived, and the definitions are meant for
split subtori. No theorem of this module needs reductivity. The theorems of the
sources, such as the root system property, are not proved here.

## Relative roots

- `relativeRoots i := roots i`, for `[IsAffineHom G.X.hom]`. The published
  `roots i` (module `Langlands.GroupScheme.Torus.Weights`) is the set of nonzero
  characters `χ` of `T` whose weight space `weightSpace i χ` in the Lie algebra
  of `G`, under the adjoint action of `T` through `i`, is nonzero. This is the
  definition of the `k`-roots of Borel–Tits 5.1 and the relative roots of
  Milne 25.13 when `i` is a maximal split torus of a connected reductive `G`.
- `mem_relativeRoots` unfolds membership; `relativeRoots_eq_roots` records the
  definition.

## Torus centralizer at the base

The subgroup functor `torusCentralizer i` is the published definition of
`Langlands.GroupScheme.Rational.TorusCentralizer`, written by Worker 176; it is
not redefined here.

- `torusCentralizer_carrier_base i`: the subgroup of `torusCentralizer i` over
  the base `Over.mk (𝟙 S)` is `centralizerPoints i`. The proof composes the
  published `mem_torusCentralizer_base_iff` (the base points of the torus
  centralizer are the points whose `innerIso` fixes `i`) with
  `mem_centralizerPoints`. This lemma holds over every base scheme.

## The relative Weyl group

- `IsClosedSubgroup.mono`: the underlying morphism of schemes of a closed
  subgroup is a monomorphism, since a closed immersion is one.
  `IsSplitSubtorus.mono` specializes this to split subtori. This supplies the
  hypothesis `[Mono i.hom.hom.left]` of the published `weylAction`.
- `conj_mem_centralizerPoints`: if `n` normalizes `i` through an automorphism
  `σ` of `T` and `z` centralizes `i`, then `n * z * n⁻¹` centralizes `i`. The
  proof composes the published `IsNormalizingPoint.mul` and
  `IsNormalizingPoint.inv`: the composite automorphism is `σ⁻¹ ∘ id ∘ σ`, which
  simplifies to the identity.
- `normal_centralizerPoints_subgroupOf`: the instance that
  `(centralizerPoints i).subgroupOf (normalizerPoints i)` is a normal subgroup
  of `normalizerPoints i`. It follows from the previous lemma.
- `relativeWeylGroup i := normalizerPoints i ⧸ (centralizerPoints i).subgroupOf
  (normalizerPoints i)`, an abbreviation, so the quotient group structure comes
  from the normality instance.

Comparison with the sources. Borel–Tits 5.1 and Milne 25.16 define the relative
Weyl group as the quotient `N_G(S)/C_G(S)` of algebraic groups. Here it is the
quotient of `k`-points `N(k)/Z(k)`, where `N(k)` and `Z(k)` are the published
`normalizerPoints` and `centralizerPoints`. That the two agree for maximal split
tori of connected reductive groups is the statement of Borel–Tits 5.3 and
Milne 25.17 that every coset meets `G(k)`; it is not proved here. The
points-quotient form is a derived reformulation.

## The span of the relative roots and the Weyl action

The linear algebra comes from the published module
`Langlands.LinearAlgebra.RationalSpan`: `toRat : M →+ ℚ ⊗[ℤ] M`, the span
`ratSpan R` of the image of a subset `R`, the extension `ratAut` of
`ℤ`-linear automorphisms to `ℚ`-linear ones, and the restriction `spanAut` of a
representation preserving `R` to the span.

- `relativeRootSpan i := ratSpan (relativeRoots i)`, the `ℚ`-subspace of
  `ℚ ⊗[ℤ] characterLattice T` spanned by the images `1 ⊗ α` of the relative
  roots. This is Milne's `ₖV ⊂ X(S) ⊗ ℚ` of 25.16.
- `weylAction_eq_one_of_mem_centralizerPoints`: a normalizing point that
  centralizes `i` acts as the identity on characters. By the published
  `weylAction_eq` it acts through the identity of `T`.
- `centralizerPoints_subgroupOf_le_ker`: the same fact as an inclusion of the
  centralizer points in the kernel of `weylAction i`.
- `weylAction_mapsTo_relativeRoots` and `weylAction_image_relativeRoots`: the
  Weyl action of every normalizing point maps the relative roots into, and in
  fact onto, the relative roots. The first is the published
  `weylAction_mem_roots_iff`; the second follows from the first applied to `n`
  and `n⁻¹` (`image_eq_of_mapsTo`).
- `map_relativeRootSpan`: the `ℚ`-linear extension `ratAut (weylAction i n)`
  maps `relativeRootSpan i` onto itself (`map_ratSpan`).
- `relativeWeylAction i : relativeWeylGroup i →* (relativeRootSpan i ≃ₗ[ℚ]
  relativeRootSpan i)`, for `[Mono i.hom.hom.left]` and
  `[IsAffineHom G.X.hom]`. It is `QuotientGroup.lift` of
  `spanAut (weylAction i) (relativeRoots i) _`; the kernel condition is
  `weylAction_eq_one_of_mem_centralizerPoints` through
  `spanAut_eq_one_of_eq_one`. For a split subtorus the monomorphism hypothesis
  is `IsSplitSubtorus.mono`.
- `relativeWeylAction_mk`, `coe_relativeWeylAction_mk_apply` and
  `relativeWeylAction_mk_toRat` compute the action of the class of `n`: on the
  span it is the restriction of `ratAut (weylAction i n)`, and it sends the
  image of a relative root `α` to the image of `weylAction i n α`. All three
  hold by `rfl`.

This is the action of Borel–Tits 5.1 on `X*(S) ⊗ ℚ`, restricted to the span of
the roots as in Milne 25.16. That this action is faithful and that its image is
the Weyl group of a root system are statements of the sources that are not
proved here.

## Generic cocharacters

- `IsGenericCocharacter i ν` for `ν : cocharacterLattice T` holds when
  `latticePairing T α ν ≠ 0` for every `α ∈ relativeRoots i`.
  `isGenericCocharacter_iff` unfolds it. The cocharacter is named `ν` because
  `λ` is a Lean keyword.

The genericity condition is a derived formulation: it is the condition that no
relative root vanishes on `ν`. For such `ν` the centralizer of `ν(𝔾ₘ)` is
expected to be the centralizer of the whole torus, as in the choice of `λ` in
the proof of Milne 25.6(b) and in Borel–Tits 4.15. That identification is not
proved here.

## Rational parabolic, Levi and unipotent subgroups

No new definitions are made for these. For a cocharacter `ν` of `T`, the
rational parabolic, Levi and unipotent subgroups attached to `ν` are the
published `Dynamic.parabolic`, `Dynamic.centralizer` and `Dynamic.unipotent`
(module `Langlands.GroupScheme.Dynamic.Basic`) of the cocharacter `ν ≫ i` of
`G`. This convention follows Milne 25.1 (every parabolic subgroup is `P(λ)`)
and Borel–Tits 4.15. The minimal parabolic subgroups of Borel–Tits 4.16 then
correspond to generic `ν` for a maximal split torus; that correspondence is
derived and is not proved here.

## Anisotropic groups

These lemmas complete the anisotropy item of the split-torus deliverable in
terms of the character lattice and the roots. They use the published
`IsAnisotropic.subsingleton_character` of
`Langlands.GroupScheme.Rational.SplitTorus`, which says that a split subtorus
of an anisotropic `G` has at most one character.

- The existing `IsAnisotropic.subsingleton_character hG hi`: if `IsAnisotropic G`
  and `IsSplitSubtorus i`, then `characterLattice T` is a subsingleton.
- `IsAnisotropic.eq_zero_of_isSplitSubtorus hG hi χ`: every character `χ` of
  `T` is `0`.
- `IsAnisotropic.top_eq_bot_of_isSplitSubtorus hG hi`: the whole character
  lattice is the zero subgroup, `(⊤ : AddSubgroup (characterLattice T)) = ⊥`.
  This is the Lean form of `characterLattice T = 0`.
- `IsAnisotropic.roots_eq_empty hG hi` and
  `IsAnisotropic.relativeRoots_eq_empty hG hi`: `roots i = ∅` and
  `relativeRoots i = ∅`, because every root is nonzero by definition.
