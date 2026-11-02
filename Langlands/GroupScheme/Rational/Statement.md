# Statements: the relative root system, the rational Bruhat decomposition and generic centralizers

Author: Worker 1220.

This module states three theorems about a maximal split torus of a connected
reductive group over a field, as `Prop`-valued definitions. Nothing is proved
here. The three theorems are the relative root system with its Weyl group, the
rational Bruhat decomposition, and the identification of the dynamic Levi
subgroup of a generic cocharacter with the torus centralizer. The conjugacy of
maximal split tori is stated in the separate module
`Langlands.GroupScheme.Rational.ConjugacyStatement`. All declarations are in
the namespace `Langlands.GroupScheme`.

Throughout, `k : Type u` is a field, `S = Spec (CommRingCat.of k)`,
`G : GroupScheme S`, `T : CommGroupScheme S` and `i : T.toGrp ⟶ G`. `G(k)`
means `Over.mk (𝟙 S) ⟶ G.X`, with the group structure on points of a group
object.

## Sources

- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 5.1–5.3 (printed pp.95–96, PDF pp.42–43): the `k`-roots `ₖΦ`, the
    relative Weyl group `ₖW = N(S)/Z(S)` and its action on `X*(S) ⊗ ℚ`;
    5.3: « Chaque composante connexe de N(S) rencontre G_k. »
  - 5.8 (printed p.98, PDF p.45): « Soient ( , ) un produit scalaire
    admissible sur X*(S) ⊗ ℚ, a ∈ ₖΦ(G) et c ∈ X*(S). Alors 2.(a, c)/(a, a)
    est un entier. En particulier, ₖΦ(G) est un système de racines [...] »
  - 5.15 (printed p.100, PDF p.47): « Le groupe G_k est réunion disjointe des
    doubles classes P_k.n.P_k (n ∈ ₖW). » Here `P = G_{ₖΦ⁺}` is a minimal
    `k`-parabolic containing the maximal split torus `S`.
  - 4.15 a) (printed pp.90–91, PDF pp.37–38): for a split torus `S` and the
    roots `Φ⁺` (resp. `Φ⁻`) of `G` relative to `S` that are positive (resp.
    negative) for an order on `X*(S)`, « G_{Φ⁺} et G_{Φ⁻} sont deux
    k-sous-groupes paraboliques opposés ayant Z(S) comme k-sous-groupe de Levi
    commun. »
  - 4.16 (printed p.91, PDF p.38): a `k`-parabolic `P` is minimal exactly when
    its radical contains a maximal split torus of `G`, and then its Levi
    subgroups are the centralizers of the maximal split tori in the radical.
- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - 25.16 (printed p.549, PDF p.565): "Let ₖV be the subspace of X(S) ⊗ ℚ
    spanned by the relative roots of (G, S). The quotient N_G(S)/C_G(S) acts
    faithfully on S, and we identify it with its image in GL_{ₖV}. Then, (a)
    the pair (ₖV, ₖΦ) is a root system; (b) every connected component of
    N_G(S) meets G(k); (c) the quotient N_G(S)/C_G(S) is a finite constant
    group scheme canonically isomorphic to the Weyl group of the root system
    (ₖV, ₖΦ)."
  - 25.17 (printed p.549, PDF p.565): the root system "is not, in general,
    reduced"; "The action of N_G(S) on ₖV factors through an isomorphism
    N_G(S)/C_G(S) → ₖW [...] Every coset of C_G(S) in N_G(S) is represented
    by an element of N_G(S)(k)."
  - Definition C.12 (printed p.610, PDF p.626): a root system in `V` is a
    finite spanning subset `R` not containing `0` such that for each `α ∈ R`
    there is a reflection `s_α` with vector `α` and `s_α(R) ⊂ R`, and
    `s_α(β) − β` is an integer multiple of `α` for all `α, β ∈ R`.
  - 25.27 (printed p.551, PDF p.567): "Let P be a parabolic subgroup of G with
    unipotent radical U, and let S be a split torus such that P = U ⋊ C_G(S).
    Then G(k) = ⊔_{w ∈ ₖW} U(k) w P(k) (Bruhat decomposition)." Here `P` is a
    minimal parabolic and `S` a maximal split torus.
  - 25.6 (printed pp.545–546, PDF pp.561–562): for a parabolic `P` and a
    maximal split torus `S` of `P`, `P ≃ R_u P ⋊ C_G(S)`; in the proof the
    cocharacter `λ` of `S` with `P = P(λ)` is chosen so that
    `C_G(S) = C_G(λ(𝔾ₘ))`.

In all these sources `G` is a connected reductive group over `k` and `S` is a
maximal split torus.

## The objects used

- `IsConnectedReductive G` is the published predicate of
  `Langlands.GroupScheme.Reductive.Basic`. Its field `hG.isAffineHom` supplies
  the instance `[IsAffineHom G.X.hom]` needed by `relativeRoots`.
- `IsMaximalSplitTorus i` and its field `isSplitSubtorus` are from
  `Langlands.GroupScheme.Rational.SplitTorus`. `hi.isSplitSubtorus.mono`
  (module `Langlands.GroupScheme.Rational.RelativeRoots`) supplies the
  instance `[Mono i.hom.hom.left]` needed by `relativeWeylAction`.
- `relativeRoots i`, `relativeRootSpan i`, `relativeWeylGroup i`,
  `relativeWeylAction i` and `IsGenericCocharacter i ν` are the definitions of
  `Langlands.GroupScheme.Rational.RelativeRoots`. The relative roots are the
  published `roots i`; the span is the `ℚ`-span of their images under
  `toRat : characterLattice T →+ ℚ ⊗[ℤ] characterLattice T` (module
  `Langlands.LinearAlgebra.RationalSpan`); the relative Weyl group is the
  quotient `normalizerPoints i ⧸ (centralizerPoints i).subgroupOf
  (normalizerPoints i)` of `k`-points, which is `N(k)/Z(k)`; a cocharacter
  `ν` is generic when `latticePairing T α ν ≠ 0` for every relative root `α`.
- `torusCentralizer i` is the subgroup functor of
  `Langlands.GroupScheme.Rational.TorusCentralizer`, by Worker 176.
- For `ν : cocharacterLattice T`, that is `ν : Gm S ⟶ T`,
  `CommGroupScheme.groupHom ν ≫ i` is the cocharacter `ν ≫ i` of `G`, and
  `Dynamic.parabolic`, `Dynamic.centralizer` (module
  `Langlands.GroupScheme.Dynamic.Basic`) are its published dynamic parabolic
  and dynamic Levi subgroup functors. The subgroup `P(k)` of `G(k)` is the
  carrier `(Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
  (Over.mk (𝟙 S))`.

The cocharacter is named `ν` rather than `λ` because `λ` is a Lean keyword, and
the root index type is named `J` because `ι` is reserved notation in the
scope of this module.

## Auxiliary predicates

### `HasRelativeRootSystem i`

For `i` with `[Mono i.hom.hom.left]` and `[IsAffineHom G.X.hom]`, and
`V = relativeRootSpan i`, `HasRelativeRootSystem i` says that there are a type
`J : Type u` with `Finite J` and a root pairing
`P : RootPairing J ℚ V (Module.Dual ℚ V)` such that

1. `P.IsRootSystem`: the roots span `V` and the coroots span its dual;
2. `P.IsCrystallographic`: every pairing of a root with a coroot is an
   integer;
3. `P.toLinearMap = Module.Dual.eval ℚ V`: the perfect pairing of `P` is the
   evaluation pairing of `V` with its dual;
4. `Subtype.val '' Set.range P.root = toRat '' relativeRoots i`: the roots of
   `P`, viewed in `ℚ ⊗[ℤ] characterLattice T`, are exactly the images
   `1 ⊗ α` of the relative roots `α`;
5. `P.weylGroup.map (RootPairing.Equiv.weightHom P) = (relativeWeylAction i).range`:
   the image of the Weyl group of `P` (the subgroup of root-pairing
   automorphisms generated by the reflections) in `V ≃ₗ[ℚ] V` is the image of
   the relative Weyl group;
6. `Function.Injective (relativeWeylAction i)`: the relative Weyl group acts
   faithfully on `V`.

### `HasRationalBruhatDecomposition i ν`

For `ν : cocharacterLattice T` and `P(k)` as above, it says:

1. every `g ∈ G(k)` can be written `g = p * n * q` with `n ∈ normalizerPoints i`
   and `p, q ∈ P(k)`;
2. for `n, n' ∈ normalizerPoints i`, there are `p, q ∈ P(k)` with
   `n' = p * n * q` if and only if `n` and `n'` have the same class in
   `relativeWeylGroup i`.

## The statements

Each statement quantifies over every field `k : Type u`, every
`G : GroupScheme S` with `hG : IsConnectedReductive G`, every commutative
`T : CommGroupScheme S` and every `i : T.toGrp ⟶ G` with
`IsMaximalSplitTorus i`.

- `RelativeRootSystemStatement`: `HasRelativeRootSystem i`.
- `RationalBruhatStatement`: for every `ν : cocharacterLattice T` with
  `IsGenericCocharacter i ν`, `HasRationalBruhatDecomposition i ν`.
- `GenericCentralizerStatement`: for every `ν : cocharacterLattice T` with
  `IsGenericCocharacter i ν`,
  `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i`.

## Correspondence with the sources

### The relative root system

- **Root systems in Mathlib.** This Mathlib has no separate `RootSystem`
  structure. A root system is a `RootPairing` together with the class
  `RootPairing.IsRootSystem` (the roots span the weight space and the coroots
  span the coweight space). So the statement asks for
  `P : RootPairing J ℚ V (Module.Dual ℚ V)` with `P.IsRootSystem`. A Mathlib
  root pairing has an injective root map `J ↪ V`, every root pairs to `2`
  with its coroot, and the reflection of every root permutes the roots and
  the coroots. Reducedness is not asserted, as in Milne 25.17: there may be
  roots `α` and `2α`.
- **Integrality.** Mathlib's root pairings over `ℚ` are not automatically
  crystallographic. The integrality condition is part of Milne's definition
  C.12 (condition RS3) and is the first assertion of Borel–Tits 5.8, so it is
  stated explicitly as `P.IsCrystallographic`.
- **The `ℚ`-form.** The sources take `ₖV ⊂ X(S) ⊗ ℚ` (Milne) or
  `X*(S) ⊗ ℚ` with an admissible scalar product (Borel–Tits). Here the
  ambient space is `ℚ ⊗[ℤ] characterLattice T`, the subspace is
  `relativeRootSpan i`, and the root system is formulated on that subspace
  with its algebraic dual and the evaluation pairing. Given a finite spanning
  set, the coroots of a root system are determined by the roots (Milne C.13,
  C.14), so fixing the pairing to be evaluation loses nothing. This
  formulation over `ℚ` is a derived reformulation of the sources.
- **Indexing.** The roots are indexed by a finite type `J`; since `P.root` is
  injective, condition 4 identifies `J` with the set of images `1 ⊗ α` of
  the relative roots.
- **The Weyl group.** Milne 25.16(c) and 25.17 identify `N_G(S)/C_G(S)`,
  acting faithfully on `ₖV`, with the Weyl group of `(ₖV, ₖΦ)`. Here the
  relative Weyl group is the quotient `N(k)/Z(k)` of `k`-points; Milne
  25.16(b), 25.17 and Borel–Tits 5.3 say that every coset of `C_G(S)` in
  `N_G(S)` has a `k`-point, so `N(k)/Z(k)` is the group of `k`-points of the
  quotient group scheme. Conditions 5 and 6 together say that
  `relativeWeylAction i` is an isomorphism of `N(k)/Z(k)` onto the image of
  the Weyl group of `P` in `GL(V)`. Mathlib's `P.weylGroup` is a subgroup of
  the automorphisms of the root pairing, so it is compared through its image
  under `RootPairing.Equiv.weightHom`, the action on the weight space `V`.

### The rational Bruhat decomposition

- **Parabolic of a generic cocharacter.** Borel–Tits 5.15 and Milne 25.27 use
  a minimal parabolic `P` containing `S`. Here `P` is the dynamic parabolic
  `P(ν)` of the cocharacter `ν ≫ i` with `ν` generic. That for generic `ν` the
  parabolic `P(ν)` is a minimal parabolic containing `S` is derived and is not
  proved here: `P(ν) = G_{Φ⁺}` for the order on `X*(S)` in which `α > 0`
  exactly when `⟨α, ν⟩ > 0` (Borel–Tits 4.15 a), Milne 25.1), and since no
  relative root vanishes on `ν` its Levi subgroup is `Z(S)`, so `P(ν)` is
  minimal by Borel–Tits 4.16.
- **Double cosets.** The sources state that `G(k)` is the disjoint union of
  the double cosets `P(k) n P(k)` over `ₖW` (Borel–Tits 5.15) or of
  `U(k) w P(k)` over `ₖW` (Milne 25.27). Since `P = U ⋊ C_G(S)` (Milne 25.6)
  and `n` normalizes `C_G(S)`, `P(k) n P(k) = U(k) n P(k)`, so the two forms
  agree. The statement here records the decomposition as covering (every `g`
  is in some `P(k) n P(k)`) and disjointness with indexing (two normalizing
  points give the same double coset exactly when they have the same class in
  `N(k)/Z(k)`). The identification of `N(k)/Z(k)` with `ₖW` is Borel–Tits 5.3
  and Milne 25.17. This double-coset form is a derived reformulation of the
  sources.

### Generic centralizers

Borel–Tits 4.15 a) says that `Z(S)` is a Levi subgroup of the parabolic
`G_{Φ⁺}`, and the proof of Milne 25.6(b) chooses a cocharacter `λ` of `S`
with `C_G(S) = C_G(λ(𝔾ₘ))`. The statement here is the form of this for every
generic `ν`: the dynamic Levi subgroup functor
`Dynamic.centralizer (ν ≫ i)`, the centralizer of `ν(𝔾ₘ)`, equals the
subgroup functor `torusCentralizer i` of points centralizing the whole torus.
It is stated as an equality of subgroup functors, that is, of the functors of
points of the two subgroups.
